output/icfp17/icfp17.vmx :
	packer build --only=vmware-iso icfp17.json

artifact107.zip : output/icfp17/icfp17.vmx
	(cd output && zip ../$@ -r icfp17)
	(cd .. && zip artifact/$@ -r ArtifactOverview.md)
