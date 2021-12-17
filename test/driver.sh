#!/bin/bash
tmp=`mktemp -d /tmp/rucc-test-XXXXXX`
trap 'rm -rf $tmp' INT TERM HUP EXIT
echo > $tmp/empty.c