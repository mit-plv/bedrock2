;; requires activating the hideshow minor mode with by running hs-minor-mode
;; Note: overrides company-coq's definition of what a block is.
;; Configures hs-hide-block and hs-show-block to hide/show ltac code between
;;  /**.   .**/

(add-to-list 'hs-special-modes-alist `(coq-mode "/\\*\\*\\." "\\.\\*\\*/" "(\\*" nil nil))
