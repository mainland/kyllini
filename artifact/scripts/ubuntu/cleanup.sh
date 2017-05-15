echo "Cleaning up apt packages"
apt-get -y autoremove
apt-get -y clean

echo "Cleaning up guest additions"
rm -rf /home/${SSH_USER}/VBoxGuestAdditions*

echo "Cleaning up dhcp leases"
rm /var/lib/dhcp/*

echo "Cleaning up udev rules"
rm -rf /etc/udev/rules.d/70-persistent-net.rules
mkdir /etc/udev/rules.d/70-persistent-net.rules
rm -rf /dev/.udev/
rm -f /lib/udev/rules.d/75-persistent-net-generator.rules
