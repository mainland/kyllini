#
# Install git and R
#
apt-get -y install git r-base r-cran-plyr r-cran-ggplot2 

#
# Install the Haskell platform
#

#apt-get -y install ghc haskell-platform

sudo apt install libgmp-dev zlib1g-dev

PLATFORM="haskell-platform-8.0.2-unknown-posix--full-x86_64.tar.gz"

wget -O "/tmp/$PLATFORM" "https://haskell.org/platform/download/8.0.2/$PLATFORM"
cd /tmp
tar xvf "$PLATFORM"
sudo ./install-haskell-platform.sh

#
# Update cabal
#
su - ${SSH_USER} <<EOF
cabal update

echo 'export PATH="/home/${SSH_USER}/.cabal/bin:\$PATH"' >>.profile
export PATH="/home/${SSH_USER}/.cabal/bin:\$PATH"
EOF

#
# Install and build kyllini
#
su - ${SSH_USER} <<EOF
git clone https://github.com/mainland/kyllini.git
cd kyllini
git checkout icfp17
./build-icfp17.sh

cd
mkdir -p Desktop
ln -sf ~/kyllini/ArtifactOverview.md ~/Desktop
EOF

#
# Modify default Unity launcher
# See:
# http://askubuntu.com/questions/363754/how-can-i-set-default-applications-in-unity-launcher-for-other-users
#
mv /home/${SSH_USER}/99_launcher.favorites.gschema.override /usr/share/glib-2.0/schemas/
chown root:root /usr/share/glib-2.0/schemas/99_launcher.favorites.gschema.override
glib-compile-schemas /usr/share/glib-2.0/schemas

#
# Change firefox's home page
#
apt-get -y install xvfb

su - ${SSH_USER} <<EOF
Xvfb :19 -screen 0 1024x768x16&
DISPLAY=:19 firefox&
sleep 5
killall firefox
killall Xvfb
echo 'user_pref("browser.startup.homepage", "${HOMEPAGE}");' >>.mozilla/firefox/*.default/prefs.js
EOF

apt-get -y remove xvfb
