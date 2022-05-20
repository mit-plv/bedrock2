;; Note: overrides company-coq's definition of what a block is.
;; Configures hs-hide-block and hs-show-block to hide/show ltac code between
;; /**.
;;   ltac_code.
;; .**/
;; If the following line is put on the first line of a .v file, this file gets loaded
;; on open-file:
;; (* -*- eval: (load-file "live_verif_setup.el"); -*- *)


;; (add-to-list 'hs-special-modes-alist `(coq-mode "/\\*\\*\\." "\\.\\*\\*/" "(\\*" nil nil))

;; Note: the end-regexp (assigned to hs-block-end-regexp) is "almost unused",
;; the real work of going from a block begin marker to go to a block end marker
;; is implemented using forward-sexp, and you have to set the hs-forward-sexp-func
;; option if you want a different one (or edit the language mode's syntax table
;; to inform forward-sexp about the block). []
;; Alternative: Declare lines as comments and use comment-hiding functionality.

;;           (forward-comment (buffer-size)

;;                (re-search-forward hs-block-start-regexp maxp t)))

;; this is not the default because it doesn't work with nested blocks,
;; so the default uses forward-sexp instead
(defun lv-hs-forward-sexp-func (arg)
  (re-search-forward hs-block-end-regexp nil t))

(defun lv-hs-adjust-block-beginning (initial)
  (- initial 4))

;; Note: We don't use blocks only comments, so we set the block-start and
;; block-end regexes to the contradictory "character followed by line start" regex
(add-to-list 'hs-special-modes-alist `(coq-mode
   "/\\*\\*\\."             ; hs-block-start-regexp
   "\\.\\*\\*/"             ; hs-block-end-regexp
   ".^"                     ; hs-c-start-regexp: for comment starts, disabled by giving
                            ; contradictory regex because if we're running hs-hide-block
                            ; inside a comment in an ltac block, we want to hide the hole
                            ; ltac block
   lv-hs-forward-sexp-func      ; custom end-of-block finder
   lv-hs-adjust-block-beginning ; hs-adjust-block-beginning
))

;; load the minor mode *after* setting the 'hs-special-modes-alist variable
;; to make sure it picks up the new value
(hs-minor-mode)

;; hs-toggle-hiding
;; (local-set-key (kbd "C-c C-k") hs-hide-block)

;; same keybinding as company-coq
(local-set-key (kbd "<backtab>") #'hs-toggle-hiding)
(local-set-key (kbd "<S-tab>") #'hs-toggle-hiding)
(local-set-key (kbd "<S-iso-lefttab>") #'hs-toggle-hiding)
