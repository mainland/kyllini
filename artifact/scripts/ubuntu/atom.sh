sudo add-apt-repository ppa:webupd8team/atom
sudo apt-get update
apt-get -y install atom

su - ${SSH_USER} <<EOF
cabal install ghc-mod hasktags

apm install language-haskell haskell-ghc-mod ide-haskell ide-haskell-cabal ide-haskell-repl ide-haskell-hasktags autocomplete-haskell
EOF

cat >.atom/config.cson <<EOF
"*":
  core:
    telemetryConsent: "no"
    themes: [
      "atom-light-ui"
      "atom-light-syntax"
    ]
EOF

chown ${SSH_USER} .atom/config.cson
