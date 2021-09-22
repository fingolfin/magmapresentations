#
# This file runs package tests. It is also referenced in the package
# metadata in PackageInfo.g.
#
LoadPackage("classicpres");
d := DirectoriesPackageLibrary("classicpres", "tst");

#TestDirectory(d[1], rec(exitGAP := true,compareFunction:="uptowhitespace"));
#
FORCE_QUIT_GAP(1);
