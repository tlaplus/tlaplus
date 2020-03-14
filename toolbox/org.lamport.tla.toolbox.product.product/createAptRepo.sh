#!/bin/bash

## Creates a basic apt repo from a single .deb file.
## Requires a passphrase-less GPG key to be available.

REPO=$1

## Remove old left-overs
rm -f $REPO/Release
rm -f $REPO/Release.gpg
rm -f $REPO/Packages
rm -f $REPO/Packages.gz
rm -f $REPO/release.conf

## Create config file for apt-archive
cat <<< '
APT::FTPArchive::Release::Components "main";
APT::FTPArchive::Release::Architectures "amd64";
APT::FTPArchive::Release::Suite "stable";
' > $REPO/release.conf

## Create Packages and Packages.gz
dpkg-scanpackages $REPO /dev/null > $REPO/Packages
dpkg-scanpackages $REPO /dev/null | gzip -9c > $REPO/Packages.gz

## Create Release file (refers to Packages*)
apt-ftparchive release -c $REPO/release.conf $REPO > $REPO/Release

## Sign Release file and create Release.gpg
gpg --armor --detach-sign -o $REPO/Release.gpg --batch --no-tty --sign $REPO/Release
