; We can't use _CoqProject because (a) it doesn't always exist and (b) there are many of them.
; We will instead use LICENSE to locate the root.  Note that if any subdirectory acquires an LICENSE file
; or if the root loses its LICENSE file, this will have to change.
((coq-mode . ((eval . (let* ((project-root (locate-dominating-file buffer-file-name "LICENSE"))
                             (coqutil-folder (expand-file-name "deps/coqutil/src" project-root))
                             (kami-folder (expand-file-name "deps/kami" project-root))
                             (riscv-coq-folder (expand-file-name "deps/riscv-coq/src" project-root))
                             (coq-path (lambda () (split-string (or (getenv "COQPATH") "") path-separator t))))
                        (unless (member coqutil-folder (funcall coq-path))
                          (setenv "COQPATH" (mapconcat #'identity (cons coqutil-folder (funcall coq-path)) path-separator))))))))
