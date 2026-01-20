/*---------------------------------------------------------------------------------------------
 *  Copyright (c) Microsoft Corporation. All rights reserved.
 *  Licensed under the MIT License. See License.txt in the project root for license information.
 *--------------------------------------------------------------------------------------------*/

import './nativeEditContext.css';
import { isFirefox, isIOS, isAndroid, isMobile } from '../../../../../base/browser/browser.js';
import { addDisposableListener, getActiveElement, getWindow, getWindowId, scheduleAtNextAnimationFrame } from '../../../../../base/browser/dom.js';
import { FastDomNode } from '../../../../../base/browser/fastDomNode.js';
import { StandardKeyboardEvent } from '../../../../../base/browser/keyboardEvent.js';
import { StandardMouseEvent } from '../../../../../base/browser/mouseEvent.js';
import { Gesture } from '../../../../../base/browser/touch.js';
import { KeyCode } from '../../../../../base/common/keyCodes.js';
import { IDisposable } from '../../../../../base/common/lifecycle.js';
import { IInstantiationService } from '../../../../../platform/instantiation/common/instantiation.js';
import { EditorOption } from '../../../../common/config/editorOptions.js';
import { EndOfLinePreference, IModelDeltaDecoration } from '../../../../common/model.js';
import { ViewConfigurationChangedEvent, ViewCursorStateChangedEvent, ViewDecorationsChangedEvent, ViewFlushedEvent, ViewLinesChangedEvent, ViewLinesDeletedEvent, ViewLinesInsertedEvent, ViewScrollChangedEvent, ViewZonesChangedEvent } from '../../../../common/viewEvents.js';
import { ViewContext } from '../../../../common/viewModel/viewContext.js';
import { RestrictedRenderingContext, RenderingContext, HorizontalPosition } from '../../../view/renderingContext.js';
import { ViewController } from '../../../view/viewController.js';
import { CopyOptions, createClipboardCopyEvent, createClipboardPasteEvent } from '../clipboardUtils.js';
import { AbstractEditContext } from '../editContext.js';
import { editContextAddDisposableListener, FocusTracker, ITypeData } from './nativeEditContextUtils.js';
import { ScreenReaderSupport } from './screenReaderSupport.js';
import { Range } from '../../../../common/core/range.js';
import { Selection } from '../../../../common/core/selection.js';
import { Position } from '../../../../common/core/position.js';
import { IVisibleRangeProvider } from '../textArea/textAreaEditContext.js';
import { PositionOffsetTransformer } from '../../../../common/core/text/positionToOffset.js';
import { EditContext } from './editContextFactory.js';
import { NativeEditContextRegistry } from './nativeEditContextRegistry.js';
import { IEditorAriaOptions } from '../../../editorBrowser.js';
import { isHighSurrogate, isLowSurrogate } from '../../../../../base/common/strings.js';
import { IME } from '../../../../../base/common/ime.js';
import { OffsetRange } from '../../../../common/core/ranges/offsetRange.js';
import { ILogService } from '../../../../../platform/log/common/log.js';
import { inputLatency } from '../../../../../base/browser/performance.js';

// Corresponds to classes in nativeEditContext.css
enum CompositionClassName {
	NONE = 'edit-context-composition-none',
	SECONDARY = 'edit-context-composition-secondary',
	PRIMARY = 'edit-context-composition-primary',
}

interface ITextUpdateEvent {
	text: string;
	selectionStart: number;
	selectionEnd: number;
	updateRangeStart: number;
	updateRangeEnd: number;
}

export class NativeEditContext extends AbstractEditContext {

	// Text area used to handle paste events
	public readonly domNode: FastDomNode<HTMLDivElement>;
	private readonly _imeTextArea: FastDomNode<HTMLTextAreaElement>;
	private readonly _editContext: EditContext;
	private readonly _screenReaderSupport: ScreenReaderSupport;
	private _previousEditContextSelection: OffsetRange = new OffsetRange(0, 0);
	private _editContextPrimarySelection: Selection = new Selection(1, 1, 1, 1);

	// Overflow guard container
	private readonly _parent: HTMLElement;
	private _decorations: string[] = [];
	private _primarySelection: Selection = new Selection(1, 1, 1, 1);


	private _targetWindowId: number = -1;
	private _scrollTop: number = 0;
	private _scrollLeft: number = 0;
	private _selectionAndControlBoundsUpdateDisposable: IDisposable | undefined;

	private readonly _focusTracker: FocusTracker;

	// Untuk penanganan touch events
	private _isTouchActive: boolean = false;
	private _touchStartPosition: { x: number; y: number } | null = null;
	private _touchStartTime: number = 0;
	private _lastTapTime: number = 0;
	private _lastTapPosition: { x: number; y: number } | null = null;
	private _touchGesture: Gesture | undefined;
	private _isScrolling: boolean = false;
	private _touchMoveThreshold: number = 10;

	constructor(
		ownerID: string,
		context: ViewContext,
		overflowGuardContainer: FastDomNode<HTMLElement>,
		private readonly _viewController: ViewController,
		private readonly _visibleRangeProvider: IVisibleRangeProvider,
		@IInstantiationService instantiationService: IInstantiationService,
		@ILogService private readonly logService: ILogService
	) {
		super(context);

		this.domNode = new FastDomNode(document.createElement('div'));
		this.domNode.setClassName(`native-edit-context`);
		
		this.domNode.setStyle('touch-action', 'manipulation');
		this.domNode.setStyle('-webkit-tap-highlight-color', 'transparent');
		this.domNode.setStyle('-webkit-user-select', 'none');
		this.domNode.setStyle('user-select', 'none');
		
		this._imeTextArea = new FastDomNode(document.createElement('textarea'));
		this._imeTextArea.setClassName(`ime-text-area`);
		this._imeTextArea.setAttribute('readonly', 'true');
		this._imeTextArea.setAttribute('tabindex', '-1');
		this._imeTextArea.setAttribute('aria-hidden', 'true');
		this.domNode.setAttribute('autocorrect', 'off');
		this.domNode.setAttribute('autocapitalize', 'off');
		this.domNode.setAttribute('autocomplete', 'off');
		this.domNode.setAttribute('spellcheck', 'false');

		this._updateDomAttributes();

		overflowGuardContainer.appendChild(this.domNode);
		overflowGuardContainer.appendChild(this._imeTextArea);
		this._parent = overflowGuardContainer.domNode;

		this._focusTracker = this._register(new FocusTracker(logService, this.domNode.domNode, (newFocusValue: boolean) => {
			logService.trace('NativeEditContext#handleFocusChange : ', newFocusValue);
			this._screenReaderSupport.handleFocusChange(newFocusValue);
			this._context.viewModel.setHasFocus(newFocusValue);
		}));

		const window = getWindow(this.domNode.domNode);
		this._editContext = EditContext.create(window);
		this.setEditContextOnDomNode();

		this._screenReaderSupport = this._register(instantiationService.createInstance(ScreenReaderSupport, this.domNode, context, this._viewController));

		this._touchGesture = new Gesture(this.domNode.domNode);

		this._registerTouchEvents();

		this._register(addDisposableListener(this.domNode.domNode, 'copy', (e) => {
			this.logService.trace('NativeEditContext#copy');

			CopyOptions.electronBugWorkaroundCopyEventHasFired = true;

			const copyEvent = createClipboardCopyEvent(e, /* isCut */ false, this._context, this.logService, isFirefox);
			this._onWillCopy.fire(copyEvent);
			if (copyEvent.isHandled) {
				return;
			}
			copyEvent.ensureClipboardGetsEditorData();
		}));
		this._register(addDisposableListener(this.domNode.domNode, 'cut', (e) => {
			this.logService.trace('NativeEditContext#cut');
			const cutEvent = createClipboardCopyEvent(e, /* isCut */ true, this._context, this.logService, isFirefox);
			this._onWillCut.fire(cutEvent);
			if (cutEvent.isHandled) {
				return;
			}
			this._screenReaderSupport.onWillCut();
			cutEvent.ensureClipboardGetsEditorData();
			this.logService.trace('NativeEditContext#cut (before viewController.cut)');
			this._viewController.cut();
		}));
		this._register(addDisposableListener(this.domNode.domNode, 'selectionchange', () => {
			inputLatency.onSelectionChange();
		}));

		this._register(addDisposableListener(this.domNode.domNode, 'keyup', (e) => this._onKeyUp(e)));
		this._register(addDisposableListener(this.domNode.domNode, 'keydown', async (e) => this._onKeyDown(e)));
		this._register(addDisposableListener(this._imeTextArea.domNode, 'keyup', (e) => this._onKeyUp(e)));
		this._register(addDisposableListener(this._imeTextArea.domNode, 'keydown', async (e) => this._onKeyDown(e)));
		this._register(addDisposableListener(this.domNode.domNode, 'beforeinput', async (e) => {
			inputLatency.onBeforeInput();
			if (e.inputType === 'insertParagraph' || e.inputType === 'insertLineBreak') {
				this._onType(this._viewController, { text: '\n', replacePrevCharCnt: 0, replaceNextCharCnt: 0, positionDelta: 0 });
			}
		}));
		this._register(addDisposableListener(this.domNode.domNode, 'paste', (e) => {
			this.logService.trace('NativeEditContext#paste');
			const pasteEvent = createClipboardPasteEvent(e);
			this._onWillPaste.fire(pasteEvent);
			if (pasteEvent.isHandled) {
				e.preventDefault();
				return;
			}
			e.preventDefault();
			if (!e.clipboardData) {
				return;
			}
			this.logService.trace('NativeEditContext#paste with id : ', pasteEvent.metadata?.id, ' with text.length: ', pasteEvent.text.length);
			if (!pasteEvent.text) {
				return;
			}
			let pasteOnNewLine = false;
			let multicursorText: string[] | null = null;
			let mode: string | null = null;
			if (pasteEvent.metadata) {
				const options = this._context.configuration.options;
				const emptySelectionClipboard = options.get(EditorOption.emptySelectionClipboard);
				pasteOnNewLine = emptySelectionClipboard && !!pasteEvent.metadata.isFromEmptySelection;
				multicursorText = typeof pasteEvent.metadata.multicursorText !== 'undefined' ? pasteEvent.metadata.multicursorText : null;
				mode = pasteEvent.metadata.mode;
			}
			this.logService.trace('NativeEditContext#paste (before viewController.paste)');
			this._viewController.paste(pasteEvent.text, pasteOnNewLine, multicursorText, mode);
		}));

		// Edit context events
		this._register(editContextAddDisposableListener(this._editContext, 'textformatupdate', (e) => this._handleTextFormatUpdate(e)));
		this._register(editContextAddDisposableListener(this._editContext, 'characterboundsupdate', (e) => this._updateCharacterBounds(e)));
		let highSurrogateCharacter: string | undefined;
		this._register(editContextAddDisposableListener(this._editContext, 'textupdate', (e) => {
			inputLatency.onInput();
			const text = e.text;
			if (text.length === 1) {
				const charCode = text.charCodeAt(0);
				if (isHighSurrogate(charCode)) {
					highSurrogateCharacter = text;
					return;
				}
				if (isLowSurrogate(charCode) && highSurrogateCharacter) {
					const textUpdateEvent: ITextUpdateEvent = {
						text: highSurrogateCharacter + text,
						selectionEnd: e.selectionEnd,
						selectionStart: e.selectionStart,
						updateRangeStart: e.updateRangeStart - 1,
						updateRangeEnd: e.updateRangeEnd - 1
					};
					highSurrogateCharacter = undefined;
					this._emitTypeEvent(this._viewController, textUpdateEvent);
					return;
				}
			}
			this._emitTypeEvent(this._viewController, e);
		}));
		this._register(editContextAddDisposableListener(this._editContext, 'compositionstart', (e) => {
			this._updateEditContext();
			this._viewController.compositionStart();
			this._context.viewModel.onCompositionStart();
		}));
		this._register(editContextAddDisposableListener(this._editContext, 'compositionend', (e) => {
			this._updateEditContext();
			this._viewController.compositionEnd();
			this._context.viewModel.onCompositionEnd();
		}));
		let reenableTracking: boolean = false;
		this._register(IME.onDidChange(() => {
			if (IME.enabled && reenableTracking) {
				this._focusTracker.resume();
				this.domNode.focus();
				reenableTracking = false;
			}
			if (!IME.enabled && this.isFocused()) {
				this._focusTracker.pause();
				this._imeTextArea.focus();
				reenableTracking = true;
			}
		}));
		this._register(NativeEditContextRegistry.register(ownerID, this));
	}

	private _registerTouchEvents(): void {
		if (!isMobile) {
			this._registerPointerEvents();
			return;
		}
		
		this._register(addDisposableListener(this.domNode.domNode, 'touchstart', (e) => {
			this._handleTouchStart(e);
		}, { passive: true }));

		this._register(addDisposableListener(this.domNode.domNode, 'touchmove', (e) => {
			this._handleTouchMove(e);
		}, { passive: true }));

		this._register(addDisposableListener(this.domNode.domNode, 'touchend', (e) => {
			this._handleTouchEnd(e);
		}, { passive: true }));

		this._register(addDisposableListener(this.domNode.domNode, 'touchcancel', (e) => {
			this._handleTouchCancel(e);
		}, { passive: true }));

		this._register(addDisposableListener(this.domNode.domNode, 'contextmenu', (e) => {
			this._handleContextMenu(e);
		}));

		this._register(addDisposableListener(this.domNode.domNode, 'gesturestart', (e) => {
			e.preventDefault();
		}));

		this._register(addDisposableListener(this.domNode.domNode, 'gesturechange', (e) => {
			e.preventDefault();
		}));

		if (this._touchGesture) {
			this._register(this._touchGesture.onTap((e) => this._handleTap(e)));
			this._register(this._touchGesture.onDoubleTap((e) => this._handleDoubleTap(e)));
			this._register(this._touchGesture.onLongPress((e) => this._handleLongPress(e)));
		}
	}

	private _registerPointerEvents(): void {
		this._register(addDisposableListener(this.domNode.domNode, 'pointerdown', (e) => {
			this._handlePointerDown(e);
		}));

		this._register(addDisposableListener(this.domNode.domNode, 'pointermove', (e) => {
			this._handlePointerMove(e);
		}));

		this._register(addDisposableListener(this.domNode.domNode, 'pointerup', (e) => {
			this._handlePointerUp(e);
		}));

		this._register(addDisposableListener(this.domNode.domNode, 'pointercancel', (e) => {
			this._handlePointerCancel(e);
		}));

		this._register(addDisposableListener(this.domNode.domNode, 'pointerleave', (e) => {
			this._handlePointerLeave(e);
		}));
	}

	private _handleTouchStart(e: TouchEvent): void {
		if (e.touches.length > 1) {
			return;
		}

		this._isTouchActive = true;
		const touch = e.touches[0];
		this._touchStartPosition = { x: touch.clientX, y: touch.clientY };
		this._touchStartTime = Date.now();
		this._isScrolling = false;

		if (!this.isFocused()) {
			this.focus();
		}

		const mouseEvent = this._createMouseEventFromTouch('mousedown', touch);
		this._viewController.dispatchMouse(mouseEvent);
	}

	private _handleTouchMove(e: TouchEvent): void {
		if (!this._isTouchActive || e.touches.length > 1) {
			return;
		}

		const touch = e.touches[0];
		
		if (this._touchStartPosition) {
			const deltaX = Math.abs(touch.clientX - this._touchStartPosition.x);
			const deltaY = Math.abs(touch.clientY - this._touchStartPosition.y);
			
			if (deltaX > this._touchMoveThreshold || deltaY > this._touchMoveThreshold) {
				this._isScrolling = true;
				
				const mouseEvent = this._createMouseEventFromTouch('mousemove', touch);
				this._viewController.dispatchMouse(mouseEvent);
				
				this._touchStartPosition = { x: touch.clientX, y: touch.clientY };
			}
		}
	}

	private _handleTouchEnd(e: TouchEvent): void {
		if (!this._isTouchActive) {
			return;
		}

		this._isTouchActive = false;
		
		if (!this._isScrolling && this._touchStartPosition && e.changedTouches.length > 0) {
			const touch = e.changedTouches[0];
			const currentTime = Date.now();
			const tapDuration = currentTime - this._touchStartTime;
			
			if (tapDuration < 300) {
				this._handleTapAtPosition(touch.clientX, touch.clientY, currentTime);
			}
			
			const mouseEvent = this._createMouseEventFromTouch('mouseup', touch);
			this._viewController.dispatchMouse(mouseEvent);
		}
		
		this._touchStartPosition = null;
		this._isScrolling = false;
	}

	private _handleTouchCancel(e: TouchEvent): void {
		this._isTouchActive = false;
		this._touchStartPosition = null;
		this._isScrolling = false;
		
		if (e.changedTouches.length > 0) {
			const mouseEvent = this._createMouseEventFromTouch('mousecancel', e.changedTouches[0]);
			this._viewController.dispatchMouse(mouseEvent);
		}
	}

	private _handleTap(e: Event): void {
		this.logService.trace('NativeEditContext#tap');
		
		if (!this.isFocused()) {
			this.focus();
		}
	}

	private _handleDoubleTap(e: Event): void {
		this.logService.trace('NativeEditContext#doubleTap');
		
		if (!this.isFocused()) {
			this.focus();
		}
		
		this._viewController.wordSelect();
	}

	private _handleLongPress(e: Event): void {
		this.logService.trace('NativeEditContext#longPress');
		
		if (!this.isFocused()) {
			this.focus();
		}
		
		this._viewController.startDragSelection();
	}

	private _handleTapAtPosition(x: number, y: number, currentTime: number): void {
		if (this._lastTapTime && this._lastTapPosition) {
			const timeDiff = currentTime - this._lastTapTime;
			const distance = Math.sqrt(
				Math.pow(x - this._lastTapPosition.x, 2) + 
				Math.pow(y - this._lastTapPosition.y, 2)
			);
			
			if (timeDiff < 500 && distance < 50) {
				this._handleDoubleTap(new Event('dbltap'));
				this._lastTapTime = 0;
				this._lastTapPosition = null;
				return;
			}
		}
		
		this._lastTapTime = currentTime;
		this._lastTapPosition = { x, y };
	}

	private _handleContextMenu(e: Event): void {
		if (isMobile) {
			e.preventDefault();
			this._viewController.showContextMenu();
		}
	}

	private _createMouseEventFromTouch(type: string, touch: Touch): StandardMouseEvent {
		const mouseEventInit: MouseEventInit = {
			clientX: touch.clientX,
			clientY: touch.clientY,
			screenX: touch.screenX,
			screenY: touch.screenY,
			button: 0,
			buttons: 1,
			ctrlKey: false,
			shiftKey: false,
			altKey: false,
			metaKey: false
		};
		
		const mouseEvent = new MouseEvent(type, mouseEventInit);
		return new StandardMouseEvent(mouseEvent);
	}

	private _handlePointerDown(e: PointerEvent): void {
		if (isMobile) return;
        
		const mouseEvent = new StandardMouseEvent(e);
		this._viewController.dispatchMouse(mouseEvent);
		
		if (e.button === 0) {
			e.preventDefault();
			e.stopPropagation();
		}
	}

	private _handlePointerMove(e: PointerEvent): void {
		if (isMobile) return;
		
		const mouseEvent = new StandardMouseEvent(e);
		this._viewController.dispatchMouse(mouseEvent);
		
		if (e.buttons & 1) {
			e.preventDefault();
			e.stopPropagation();
		}
	}

	private _handlePointerUp(e: PointerEvent): void {
		if (isMobile) return;
		
		const mouseEvent = new StandardMouseEvent(e);
		this._viewController.dispatchMouse(mouseEvent);
		
		if (e.button === 0) {
			e.preventDefault();
			e.stopPropagation();
		}
	}

	private _handlePointerCancel(e: PointerEvent): void {
		if (isMobile) return;
		
		this._viewController.dispatchMouse(new StandardMouseEvent(e));
	}

	private _handlePointerLeave(e: PointerEvent): void {
		if (isMobile) return;
	}

	public override dispose(): void {
		this._touchGesture?.dispose();
		
		this.domNode.domNode.editContext = undefined;
		this.domNode.domNode.blur();
		this.domNode.domNode.remove();
		this._imeTextArea.domNode.remove();
		this._selectionAndControlBoundsUpdateDisposable?.dispose();
		this._selectionAndControlBoundsUpdateDisposable = undefined;
		super.dispose();
	}

	public setAriaOptions(options: IEditorAriaOptions): void {
		this._screenReaderSupport.setAriaOptions(options);
	}

	public getLastRenderData(): Position | null {
		return this._primarySelection.getPosition();
	}

	public override prepareRender(ctx: RenderingContext): void {
		this._screenReaderSupport.prepareRender(ctx);
		this._updateSelectionAndControlBoundsData(ctx);
	}

	public override onDidRender(): void {
		this._updateSelectionAndControlBoundsAfterRender();
	}

	public render(ctx: RestrictedRenderingContext): void {
		this._screenReaderSupport.render(ctx);
	}

	public override onCursorStateChanged(e: ViewCursorStateChangedEvent): boolean {
		this._primarySelection = e.modelSelections[0] ?? new Selection(1, 1, 1, 1);
		this._screenReaderSupport.onCursorStateChanged(e);
		this._updateEditContext();
		return true;
	}

	public override onConfigurationChanged(e: ViewConfigurationChangedEvent): boolean {
		this._screenReaderSupport.onConfigurationChanged(e);
		this._updateDomAttributes();
		return true;
	}

	public override onDecorationsChanged(e: ViewDecorationsChangedEvent): boolean {
		return true;
	}

	public override onFlushed(e: ViewFlushedEvent): boolean {
		return true;
	}

	public override onLinesChanged(e: ViewLinesChangedEvent): boolean {
		this._updateEditContextOnLineChange(e.fromLineNumber, e.fromLineNumber + e.count - 1);
		return true;
	}

	public override onLinesDeleted(e: ViewLinesDeletedEvent): boolean {
		this._updateEditContextOnLineChange(e.fromLineNumber, e.toLineNumber);
		return true;
	}

	public override onLinesInserted(e: ViewLinesInsertedEvent): boolean {
		this._updateEditContextOnLineChange(e.fromLineNumber, e.toLineNumber);
		return true;
	}

	private _updateEditContextOnLineChange(fromLineNumber: number, toLineNumber: number): void {
		if (this._editContextPrimarySelection.endLineNumber < fromLineNumber || this._editContextPrimarySelection.startLineNumber > toLineNumber) {
			return;
		}
		this._updateEditContext();
	}

	public override onScrollChanged(e: ViewScrollChangedEvent): boolean {
		this._scrollLeft = e.scrollLeft;
		this._scrollTop = e.scrollTop;
		return true;
	}

	public override onZonesChanged(e: ViewZonesChangedEvent): boolean {
		return true;
	}

	public handleWillPaste(): void {
		this.logService.trace('NativeEditContext#handleWillPaste');
		this._prepareScreenReaderForPaste();
	}

	private _prepareScreenReaderForPaste(): void {
		this._screenReaderSupport.onWillPaste();
	}

	public handleWillCopy(): void {
		this.logService.trace('NativeEditContext#handleWillCopy');
		this.logService.trace('NativeEditContext#isFocused : ', this.domNode.domNode === getActiveElement());
	}

	public writeScreenReaderContent(): void {
		this._screenReaderSupport.writeScreenReaderContent();
	}

	public isFocused(): boolean {
		return this._focusTracker.isFocused;
	}

	public focus(): void {
		this._focusTracker.focus();
		this.refreshFocusState();
	}

	public refreshFocusState(): void {
		this._focusTracker.refreshFocusState();
	}

	public setEditContextOnDomNode(): void {
		const targetWindow = getWindow(this.domNode.domNode);
		const targetWindowId = getWindowId(targetWindow);
		if (this._targetWindowId !== targetWindowId) {
			this.domNode.domNode.editContext = this._editContext;
			this._targetWindowId = targetWindowId;
		}
	}

	private _onKeyUp(e: KeyboardEvent) {
		inputLatency.onKeyUp();
		this._viewController.emitKeyUp(new StandardKeyboardEvent(e));
	}

	private _onKeyDown(e: KeyboardEvent) {
		inputLatency.onKeyDown();
		const standardKeyboardEvent = new StandardKeyboardEvent(e);
		if (standardKeyboardEvent.keyCode === KeyCode.KEY_IN_COMPOSITION) {
			standardKeyboardEvent.stopPropagation();
		}
		this._viewController.emitKeyDown(standardKeyboardEvent);
	}

	private _updateDomAttributes(): void {
		const options = this._context.configuration.options;
		this.domNode.domNode.setAttribute('tabindex', String(options.get(EditorOption.tabIndex)));
		
		if (isMobile) {
			this.domNode.setAttribute('inputmode', 'text');
			
			if (isIOS) {
				const autoClosingBrackets = options.get(EditorOption.autoClosingBrackets);
				const autoClosingQuotes = options.get(EditorOption.autoClosingQuotes);
				if (!autoClosingBrackets && !autoClosingQuotes) {
					this.domNode.setAttribute('autocorrect', 'off');
				}
			}
		}
	}

	private _updateEditContext(): void {
		const editContextState = this._getNewEditContextState();
		if (!editContextState) {
			return;
		}
		this._editContext.updateText(0, Number.MAX_SAFE_INTEGER, editContextState.text ?? ' ');
		this._editContext.updateSelection(editContextState.selectionStartOffset, editContextState.selectionEndOffset);
		this._editContextPrimarySelection = editContextState.editContextPrimarySelection;
		this._previousEditContextSelection = new OffsetRange(editContextState.selectionStartOffset, editContextState.selectionEndOffset);
	}

	private _emitTypeEvent(viewController: ViewController, e: ITextUpdateEvent): void {
		if (!this._editContext) {
			return;
		}
		const selectionEndOffset = this._previousEditContextSelection.endExclusive;
		const selectionStartOffset = this._previousEditContextSelection.start;
		this._previousEditContextSelection = new OffsetRange(e.selectionStart, e.selectionEnd);

		let replaceNextCharCnt = 0;
		let replacePrevCharCnt = 0;
		if (e.updateRangeEnd > selectionEndOffset) {
			replaceNextCharCnt = e.updateRangeEnd - selectionEndOffset;
		}
		if (e.updateRangeStart < selectionStartOffset) {
			replacePrevCharCnt = selectionStartOffset - e.updateRangeStart;
		}
		let text = '';
		if (selectionStartOffset < e.updateRangeStart) {
			text += this._editContext.text.substring(selectionStartOffset, e.updateRangeStart);
		}
		text += e.text;
		if (selectionEndOffset > e.updateRangeEnd) {
			text += this._editContext.text.substring(e.updateRangeEnd, selectionEndOffset);
		}
		let positionDelta = 0;
		if (e.selectionStart === e.selectionEnd && selectionStartOffset === selectionEndOffset) {
			positionDelta = e.selectionStart - (e.updateRangeStart + e.text.length);
		}
		const typeInput: ITypeData = {
			text,
			replacePrevCharCnt,
			replaceNextCharCnt,
			positionDelta
		};
		this._onType(viewController, typeInput);
	}

	private _onType(viewController: ViewController, typeInput: ITypeData): void {
		if (typeInput.replacePrevCharCnt || typeInput.replaceNextCharCnt || typeInput.positionDelta) {
			viewController.compositionType(typeInput.text, typeInput.replacePrevCharCnt, typeInput.replaceNextCharCnt, typeInput.positionDelta);
		} else {
			viewController.type(typeInput.text);
		}
	}

	private _getNewEditContextState(): { text: string; selectionStartOffset: number; selectionEndOffset: number; editContextPrimarySelection: Selection } | undefined {
		const editContextPrimarySelection = this._primarySelection;
		const model = this._context.viewModel.model;
		if (!model.isValidRange(editContextPrimarySelection)) {
			return;
		}
		const primarySelectionStartLine = editContextPrimarySelection.startLineNumber;
		const primarySelectionEndLine = editContextPrimarySelection.endLineNumber;
		const endColumnOfEndLineNumber = model.getLineMaxColumn(primarySelectionEndLine);
		const rangeOfText = new Range(primarySelectionStartLine, 1, primarySelectionEndLine, endColumnOfEndLineNumber);
		const text = model.getValueInRange(rangeOfText, EndOfLinePreference.TextDefined);
		const selectionStartOffset = editContextPrimarySelection.startColumn - 1;
		const selectionEndOffset = text.length + editContextPrimarySelection.endColumn - endColumnOfEndLineNumber;
		return {
			text,
			selectionStartOffset,
			selectionEndOffset,
			editContextPrimarySelection
		};
	}

	private _editContextStartPosition(): Position {
		return new Position(this._editContextPrimarySelection.startLineNumber, 1);
	}

	private _handleTextFormatUpdate(e: TextFormatUpdateEvent): void {
		if (!this._editContext) {
			return;
		}
		const formats = e.getTextFormats();
		const editContextStartPosition = this._editContextStartPosition();
		const decorations: IModelDeltaDecoration[] = [];
		formats.forEach(f => {
			const textModel = this._context.viewModel.model;
			const offsetOfEditContextText = textModel.getOffsetAt(editContextStartPosition);
			const startPositionOfDecoration = textModel.getPositionAt(offsetOfEditContextText + f.rangeStart);
			const endPositionOfDecoration = textModel.getPositionAt(offsetOfEditContextText + f.rangeEnd);
			const decorationRange = Range.fromPositions(startPositionOfDecoration, endPositionOfDecoration);
			const thickness = f.underlineThickness.toLowerCase();
			let decorationClassName: string = CompositionClassName.NONE;
			switch (thickness) {
				case 'thin':
					decorationClassName = CompositionClassName.SECONDARY;
					break;
				case 'thick':
					decorationClassName = CompositionClassName.PRIMARY;
					break;
			}
			decorations.push({
				range: decorationRange,
				options: {
					description: 'textFormatDecoration',
					inlineClassName: decorationClassName,
				}
			});
		});
		this._decorations = this._context.viewModel.model.deltaDecorations(this._decorations, decorations);
	}

	private _linesVisibleRanges: HorizontalPosition | null = null;
	private _updateSelectionAndControlBoundsData(ctx: RenderingContext): void {
		const viewSelection = this._context.viewModel.coordinatesConverter.convertModelRangeToViewRange(this._primarySelection);
		if (this._primarySelection.isEmpty()) {
			const linesVisibleRanges = ctx.visibleRangeForPosition(viewSelection.getStartPosition());
			this._linesVisibleRanges = linesVisibleRanges;
		} else {
			this._linesVisibleRanges = null;
		}
	}

	private _updateSelectionAndControlBoundsAfterRender(): void {
		if (this._selectionAndControlBoundsUpdateDisposable) {
			return;
		}
		const targetWindow = getWindow(this.domNode.domNode);
		this._selectionAndControlBoundsUpdateDisposable = scheduleAtNextAnimationFrame(targetWindow, () => {
			this._selectionAndControlBoundsUpdateDisposable = undefined;
			this._applySelectionAndControlBounds();
		});
	}

	private _applySelectionAndControlBounds(): void {
		const options = this._context.configuration.options;
		const contentLeft = options.get(EditorOption.layoutInfo).contentLeft;

		const viewSelection = this._context.viewModel.coordinatesConverter.convertModelRangeToViewRange(this._primarySelection);
		const verticalOffsetStart = this._context.viewLayout.getVerticalOffsetForLineNumber(viewSelection.startLineNumber);
		const verticalOffsetEnd = this._context.viewLayout.getVerticalOffsetAfterLineNumber(viewSelection.endLineNumber);

		const parentBounds = this._parent.getBoundingClientRect();
		const top = parentBounds.top + verticalOffsetStart - this._scrollTop;
		const height = verticalOffsetEnd - verticalOffsetStart;
		let left = parentBounds.left + contentLeft - this._scrollLeft;
		let width: number;

		if (this._primarySelection.isEmpty()) {
			if (this._linesVisibleRanges) {
				left += this._linesVisibleRanges.left;
			}
			width = 0;
		} else {
			width = parentBounds.width - contentLeft;
		}

		const selectionBounds = new DOMRect(left, top, width, height);
		this._editContext.updateSelectionBounds(selectionBounds);
		this._editContext.updateControlBounds(selectionBounds);
	}

	private _updateCharacterBounds(e: CharacterBoundsUpdateEvent): void {
		const options = this._context.configuration.options;
		const typicalHalfWidthCharacterWidth = options.get(EditorOption.fontInfo).typicalHalfwidthCharacterWidth;
		const contentLeft = options.get(EditorOption.layoutInfo).contentLeft;
		const parentBounds = this._parent.getBoundingClientRect();

		const characterBounds: DOMRect[] = [];
		const offsetTransformer = new PositionOffsetTransformer(this._editContext.text);
		for (let offset = e.rangeStart; offset < e.rangeEnd; offset++) {
			const editContextStartPosition = offsetTransformer.getPosition(offset);
			const textStartLineOffsetWithinEditor = this._editContextPrimarySelection.startLineNumber - 1;
			const characterStartPosition = new Position(textStartLineOffsetWithinEditor + editContextStartPosition.lineNumber, editContextStartPosition.column);
			const characterEndPosition = characterStartPosition.delta(0, 1);
			const characterModelRange = Range.fromPositions(characterStartPosition, characterEndPosition);
			const characterViewRange = this._context.viewModel.coordinatesConverter.convertModelRangeToViewRange(characterModelRange);
			const characterLinesVisibleRanges = this._visibleRangeProvider.linesVisibleRangesForRange(characterViewRange, true) ?? [];
			const lineNumber = characterViewRange.startLineNumber;
			const characterVerticalOffset = this._context.viewLayout.getVerticalOffsetForLineNumber(lineNumber);
			const top = parentBounds.top + characterVerticalOffset - this._scrollTop;

			let left = 0;
			let width = typicalHalfWidthCharacterWidth;
			if (characterLinesVisibleRanges.length > 0) {
				for (const visibleRange of characterLinesVisibleRanges[0].ranges) {
					left = visibleRange.left;
					width = visibleRange.width;
					break;
				}
			}
			const lineHeight = this._context.viewLayout.getLineHeightForLineNumber(lineNumber);
			characterBounds.push(new DOMRect(parentBounds.left + contentLeft + left - this._scrollLeft, top, width, lineHeight));
		}
		this._editContext.updateCharacterBounds(e.rangeStart, characterBounds);
	}
}