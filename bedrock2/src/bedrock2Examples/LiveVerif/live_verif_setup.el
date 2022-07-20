;; Note: overrides company-coq's definition of what a block is.
;; Configures hs-hide-block and hs-show-block to hide/show ltac code between
;; /**.
;;   ltac_code.
;; .**/
;; If the following line is put on the first line of a .v file, this file gets loaded
;; on open-file:
;; (* -*- eval: (load-file "live_verif_setup.el"); -*- *)

;; Note: the end-regexp (assigned to hs-block-end-regexp) is "almost unused",
;; the real work of going from a block begin marker to go to a block end marker
;; is implemented using forward-sexp, and you have to set the hs-forward-sexp-func
;; option if you want a different one (or edit the language mode's syntax table
;; to inform forward-sexp about the block).

;; In hideshow, this is not the default because it doesn't work with nested blocks,
;; so the default uses forward-sexp instead.
(defun lv-hs-forward-sexp-func (arg)
  (re-search-forward hs-block-end-regexp nil))

(add-to-list 'hs-special-modes-alist `(coq-mode
   "/\\*\\*\\."             ; hs-block-start-regexp
   "\\.\\*\\*/"             ; hs-block-end-regexp
   ".^"                     ; hs-c-start-regexp: for comment starts, disabled by giving
                            ; contradictory regex because if we're running hs-hide-block
                            ; inside a comment in an ltac block, we want to hide the hole
                            ; ltac block
   lv-hs-forward-sexp-func  ; custom end-of-block finder
   nil                      ; hs-adjust-block-beginning: unused because after adjusting,
                            ; hideshow insists to still go to the end of line
))

;; load the minor mode *after* setting the 'hs-special-modes-alist variable
;; to make sure it picks up the new value
(hs-minor-mode)

;; for debugging
;; (defvar dbg-latest-overlay nil)
;; (defun lv-hs-set-up-overlay (ov)
;;  (progn
;;    (message "start: %d, end: %d, display: %s"
;;             (overlay-start ov) (overlay-end ov) (overlay-get ov 'display))
;;    (setq dbg-latest-overlay ov)))

(defun lv-hs-set-up-overlay (ov)
  ; (move-overlay ov (overlay-start ov) (- (overlay-end ov) 1)))
  ; u2026 = triple dot in one char
  (overlay-put ov 'display (propertize "\u2026" 'face 'font-lock-type-face)))

(setq hs-set-up-overlay #'lv-hs-set-up-overlay)

;; hs-toggle-hiding
;; (local-set-key (kbd "C-c C-k") hs-hide-block)

(defun lv-toggle-hiding ()
  (interactive)
  (hs-life-goes-on
   (if (hs-already-hidden-p)
       (hs-show-block t) ; pass t to make point jump to end of hidden region
     (hs-hide-block))))

;; same keybinding as company-coq
(local-set-key (kbd "<backtab>") #'lv-toggle-hiding)
(local-set-key (kbd "<S-tab>") #'lv-toggle-hiding)
(local-set-key (kbd "<S-iso-lefttab>") #'lv-toggle-hiding)
