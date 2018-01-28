;;; etiml.el --- Support for ETiML files           -*- lexical-binding: t; -*-

;; Copyright (C) 2016  Clément Pit-Claudel

;; Author: Clément Pit-Claudel <clement.pitclaudel@live.com>
;; Keywords: languages
;; Package-Requires: ((sml-mode "27") (emacs "24.3"))
;; Version: 0.1

;;; Commentary:


;;; Code:

(require 'sml-mode)
(require 'flycheck)

;;; Constants

(defconst etiml--this-file (or load-file-name
                          (bound-and-true-p byte-compile-current-file)
                          (buffer-file-name))
  "Full path of this script.")

(defconst etiml--default-executable
  (expand-file-name "main.sh"
                    (file-name-directory etiml--this-file)))

(defconst etiml--stdlib
  (expand-file-name "examples/stdlib.pkg"
                    (file-name-directory etiml--this-file)))

;;; Customizable settings

(defvar etiml-prettify-symbols-alist '(("fn" . ?λ)
                                  ("/\\" . ?∧) ("\\/" . ?∨)
                                  ("->" . ?→) ("=>" . ?⇒)
                                  ("<=" . ?≤) (">=" . ?≥) ("<>" . ?≠) ("==" . ?≡) ("<==" . ?≦) 
                                  ("->>" . ?↠) ("-->" . ?⟶)
                                  ("Nat" . ?ℕ) ("Bool" . ?𝔹)
                                  ("forall" . ?∀) ("|>" . ?▹)
                                  ("'a" . ?α) ("'b" . ?β) ("'c" . ?γ)
                                  ("'d" . ?δ) ("'e" . ?ε) ("'v" . ?ν)
                                  ))

(defvar etiml-box-width -1)

;;; Font-locking and mode definition

(defun etiml--setup-font-lock ()
  "Set font-lock–related settings for ETiML."
  (setq prettify-symbols-alist etiml-prettify-symbols-alist)
  (let ((etiml-builtins '("BigO" "ceil" "floor" "b2n" "forall" "never" "log2" "log10"))
        (etiml-keywords '("return" "using" "absidx" "returns" "public" "private" "external" "internal" "payable" "constant" "pure" "view" "guarded_by" "forward_to" "inherited_from" "contract" "endcontract" "end_contract" "interface" "endinterface" "end_interface" "endif" "for" "endfor" "while" "endwhile" "event" "map" "array" "vector" "address" "uint" "uint16" "uint32" "uint64" "uint256" "bytes" "bytes32" "bool" "true" "false" "sha3" "sha256" "ecrecover" "super" "ref" "zero_value" "empty" "set" "modify" "days" "ether" "assert" "require" "throw" "pragma" "not" "indexed" "string")))
    (font-lock-add-keywords
     nil
     `(("\\_<'[a-z]\\_>" 0 '((:slant italic)))
       (,(concat "\\_<\\(absidx\\)\\s-+\\(" sml-id-re "\\)")
        (1 font-lock-keyword-face)
        (2 font-lock-function-name-face))
       ("\\(\\$(\\)\\(.*?\\)\\()\\)"
        (1 '((:weight bold)))
        (2 '((:slant italic)))
        (3 '((:weight bold))))
       ("\\([@]\\)\\w+\\>"
        (1 '((:weight bold))))
       ("\\([$]\\) *\\(\\(\\w\\|\\s_\\)+\\)\\>"
        (1 '((:weight bold)))
        (2 '((:slant italic))))
       ("\\({\\)\\(.*?\\)\\(}\\)"
        (1 '((:weight bold)))
        (3 '((:weight bold))))
       ("\\(\\[\\)\\(.*?\\)\\(\\]\\)"
        (1 '((:weight bold)))
        (3 '((:weight bold))))
       ("\\_<\\([A-Z][a-zA-Z']*\\)\\([.]\\|\\_>\\)" 1 font-lock-type-face)
       (,(regexp-opt etiml-builtins 'symbols) 0 'font-lock-builtin-face)
       (,(regexp-opt etiml-keywords 'symbols) 0 'font-lock-keyword-face)
       ("\\(--\\)\\( .+? \\)\\(-->\\)"
        (1 (ignore (compose-region (match-beginning 1) (match-end 1) ?–)))
        (2 `((:box (:line-width ,etiml-box-width))) append)
        (3 (ignore (compose-region (match-beginning 3) (match-end 3) ?→))))
       ("\\_<log\\(2\\|10\\)\\_>"
        (1 '(face nil display (raise -0.25)) append)))
     'append)))

(define-derived-mode etiml-mode sml-mode "ETiML"
  (etiml--setup-font-lock)
  ;; (make-variable-buffer-local 'tooltip-functions)
  ;; (push #'etiml--tooltip-help-tips tooltip-functions)
  (prettify-symbols-mode))

(add-to-list 'auto-mode-alist '("\\.etiml\\'" . etiml-mode))

;;; Flycheck

(defun etiml--fontify-str (str &optional postproc)
  "Fontify STR as ETiML code.
Run POSTPROC after fontifying if non-nil."
  (with-temp-buffer
    (delay-mode-hooks (etiml-mode))
    (setq delayed-mode-hooks nil)
    (insert str)
    (if (fboundp 'font-lock-ensure)
        (font-lock-ensure)
      (with-no-warnings (font-lock-fontify-buffer)))
    (when postproc
      (funcall postproc))
    (buffer-string)))

(defun etiml--fontify-message-postproc ()
  "Mark parts of error message MSG."
  (goto-char (point-min))
  (while (not (eobp))
    (unless (looking-at-p "  ")
      (remove-text-properties (point-at-bol) (point-at-eol) '(face nil font-lock-face nil)))
    (forward-line)))

(defun etiml--error-filter (errors)
  "Fontify messages of ERRORS and adjust column number."
  (flycheck-sanitize-errors errors)
  (flycheck-increment-error-columns errors)
  (dolist (err errors)
    (let ((message (flycheck-error-message err)))
      (when message
        (setq message (replace-regexp-in-string "^  " "" message nil t))
        (setf (flycheck-error-message err)
              (etiml--fontify-str message #'etiml--fontify-message-postproc)))))
  errors)

(flycheck-def-executable-var etiml etiml--default-executable)

(flycheck-define-command-checker 'etiml
  "A ETiML checker."
  :command `(,etiml--default-executable (eval etiml--stdlib) source-inplace)
  :error-patterns
  '((error line-start "File " (file-name) ", line " line "-" (one-or-more digit)
           ", characters " column "-" (one-or-more digit) ":\n"
           (message (one-or-more "  " (zero-or-more not-newline) "\n"))))
  :error-filter #'etiml--error-filter
  :modes '(etiml-mode))

(add-to-list 'flycheck-checkers 'etiml)

(provide 'etiml)
;;; etiml.el ends here
