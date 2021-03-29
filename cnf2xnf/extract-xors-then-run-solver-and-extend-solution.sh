#!/bin/sh
#tmp="/tmp/extor$$"
#tmp="/tmp/extor"
tmp=/tmp/
trap "rm -f $tmp*" 2 3 9 15
die () {
  echo "error: $*" 1>&2
  exit 1
}
[ $# -lt 1 ] && die "solver argument missing"
[ $# -gt 2 ] && die "too many arguments"
[ -x "$1" ] || die "can not execute '$1'"
solver="$1"
if [ $# = 1 ]
then
  cnf="-"
elif [ -f "$2" ]
then
  cnf="$2"
else
  die "can not access '$2'"
fi
extracted=${tmp}extracted
extension=${tmp}extension
./cnf2xnf "$cnf" $extracted $extension
witness=${tmp}witness
case $solver in
  yalsat*|xorsat*|*yalsat|*xorsat)options=" --witness";;
esac
$solver$options $extracted |tee -i $witness|sed -e '/^v/d;s/^s/c/'
./extor $extension $witness
status=$?
#rm -f $tmp*
exit $status
