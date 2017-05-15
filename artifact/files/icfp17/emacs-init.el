(require 'package)
(package-initialize)
(setq package-archives
      '(("gnu" . "http://elpa.gnu.org/packages/")
	("melpa" . "http://melpa.milkbox.net/packages/")))

(package-list-packages)

(mapc
 (lambda (package)
   (or (package-installed-p package)
       (package-install package)))
 '(haskell-mode
   magit
   org
   python-mode
   quack
   sml-mode))
