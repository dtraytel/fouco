#!/bin/bash --

NAME=$1
EDIT=$2
BASE=`ls ${NAME} | grep "[0-9][0-9]*\.thy" -o  | tr -d ".thy" | sort -n | tail -n1`

STEP=$[${BASE}+1]

for file in `ls | grep "_step.thy"`; do
  cp ${file} ${NAME}/${NAME}_`echo ${file} | sed "s/_step/${STEP}/g"`;
done

cd ${NAME}

for file in `ls | grep "${STEP}"`; do
  sed -i "s/_base/${BASE}/g" ${file};
  sed -i "s/_step/${STEP}/g" ${file};
  sed -i "s/^theory  */theory ${NAME}_/g" ${file};
  sed -i "s/^imports  */imports ${NAME}_/g" ${file};
done

cd ..

$EDIT $NAME/${NAME}_Input${STEP}.thy  $NAME/${NAME}_Op_Input${STEP}.thy  &
