The script below shows how the .jq and .md files are combined and turned into
a GitHub release.  A copy of this script is executed by our build machine when
a release build has been manually approved.  In an ideal world, this would be
integrated into the maven build but it is probably not worth it.

-----------------

#!/bin/bash

cd $WORKSPACE/general/docs/changelogs

## Convert the Markdown changelog into a single JSON string.
#cat ch1_5_8.md | jq  --raw-input --slurp . > ch1_5_8.json

## Read the converted markdown into the Github release JSON template
#jq -n --argjson changelog "$(cat ch1_5_8.json)" -f gh-1_5_8.jq > gh-1_5_8.json

## Two above as one-liner without intermediate file.
$(jq -n --argjson changelog "$(cat ch1_5_8.md | jq  --raw-input --slurp .)" -f gh-1_5_8.jq > gh-1_5_8.json)

## Post the new release to Github and read the release ID from the response.
#DRAFT_RELEAES=$(curl -sS -H "Authorization: token 123456790" https://api.github.com/repos/tlaplus/tlaplus/releases -d @gh-1_5_8.json -X POST --header "Content-Type: application/json" | jq '.| select(.draft==true and .name=="The Zenobius release") | .id')

## Get id of existing draft release with given name.
DRAFT_RELEASE=$(curl -sS -H "Authorization: token 1234567890" https://api.github.com/repos/tlaplus/tlaplus/releases --header "Content-Type: application/json" | jq '.[]| select(.draft==true and .name=="The Zenobius release") | .id')
echo $DRAFT_RELEASE

## Update draft release with latest changelog in case it changed.
## https://developer.github.com/v3/repos/releases/#edit-a-release
curl -sS -H "Authorization: token 1234567890" https://api.github.com/repos/tlaplus/tlaplus/releases/$DRAFT_RELEASE -d @gh-1_5_8.json -X PATCH --header "Content-Type: application/json"

## iterate over zips and tla2tools.jar and upload to release (reverse order for TLA* to show up first).
cd /home/jenkins/jobs/Release-HEAD-Toolbox.product.standalone/configurations/axis-os/master/lastStable/archive
for f in $(find . \( -name "*.zip" -o -name "tla2tools.jar" \) | tac); do BASE=$(basename $f) && curl -s -X POST -H "Content-Type: application/zip" -H "Authorization: token 1234567890" https://uploads.github.com/repos/tlaplus/tlaplus/releases/$DRAFT_RELEASE/assets?name=$BASE --upload-file $f; done
