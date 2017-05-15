apt-get -y install open-vm-tools open-vm-tools-desktop

echo -n ".host:/ /mnt/hgfs fuse.vmhgfs-fuse allow_other,uid=1000,gid=1000,auto_unmount,defaults 0 0" >> /etc/fstab
