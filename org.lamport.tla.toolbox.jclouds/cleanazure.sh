#!/bin/bash

## Get the output of `azure vm list`, extract the vm ids and loop over the result
## Terminate/delete each VM including its disk image (-d)
IMAGES=`azure vm list --json | grep 'VMName'| cut -d '"' -f 4`
for i in $IMAGES; do
    azure vm delete --quiet --blob-delete $i
done

## Get the output of `azure storage account list`
## Quietly (no confirmation prompt) delete all accounts
ACCOUNTS=`azure storage account list --json | grep '"name"' | cut -d '"' -f 4`
for a in $ACCOUNTS; do
    azure storage account delete --quiet $a
done
