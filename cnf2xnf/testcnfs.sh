#!/bin/sh
run () {
  expected=$1
  cnf=cnfs/$2.cnf
  xnf=cnfs/$2.xnf
  log=cnfs/$2.log
  err=cnfs/$2.err
  cmd="./cnf2xnf $cnf $xnf"
  printf "$cmd # expected '$expected' XORs"
  ./cnf2xnf $cnf $xnf 1>$log 2>$err
  status=$?
  if [ $status = 0 ]
  then
    extracted="`awk '/extracted/{print $3}' $log`"
    if [ "$expected" = "$extracted" ]
    then
      echo " OK"
    else
      echo " but extracted '$extracted'"
      echo "testcnfs.sh: error: '$cmd' FAILED"
      exit 1
    fi
  else
     echo " status '$status'"
      echo "testcnfs.sh: error: '$cmd' FAILED"
     exit 1
  fi
}

run 0 true
run 0 false

run 1 xor1
run 1 xor2
run 1 xor3
run 2 xor4
run 1 xor5

run 1 mixed1
run 1 mixed2

run 0 missing1
run 0 missing2
run 0 missing3

run 0 and1

run 1 aig1

run 3 regr1
