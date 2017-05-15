#
# Install emacs
#
apt-get -y install emacs24

su -c "emacs --script /tmp/emacs-init.el" ${SSH_USER} 

#
# Install vim
#
apt-get -y install vim-gnome
