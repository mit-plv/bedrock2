((coq-mode
  (eval . (local-set-key (kbd "C-c C-k") (lambda ()
    (interactive)
    (insert (make-string (max 0 (- 77 (current-column))) ?\s))
    (insert "/*.")
    (newline)
    (proof-goto-point)
    (insert "#*/ "))))))
