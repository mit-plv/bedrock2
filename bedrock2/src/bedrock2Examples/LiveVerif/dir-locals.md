Once the framework is more mature, it might be helpful to put the following into a `.dir-locals.el`:

```
((coq-mode
  (eval . (local-set-key (kbd "C-c C-k") (lambda ()
    (interactive)
    (insert (make-string (max 0 (- 77 (current-column))) ?\s))
    (insert "/*.")
    (newline)
    (proof-goto-point)
    (insert "#*/ "))))))
```

However, it overrides `.dir-locals.el` that are further up.
