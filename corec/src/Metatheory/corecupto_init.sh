#!/bin/bash --

NAME=$1
EDIT=$2

if [ -d ${NAME} ]; then
  find ${NAME} -type f -not -name \*Input\*.thy -exec rm {} \;
else
  mkdir ${NAME}
fi

SAFE=`find ${NAME} -type f`

for file in Incremental Prelim Behavior_BNF; do
  cp ${file}.thy ${NAME}/${NAME}_${file}.thy;
done

for file in `ls | grep "_base.thy"`; do
  file2=${NAME}/${NAME}_`echo ${file} | sed "s/_base/0/g"`
  if [[ ${SAFE} =~ ${file2} ]]; then
    cp -n ${file} ${file2};
  else
    cp ${file} ${file2};
  fi
done

cd ${NAME}

for file in `ls`; do
  if ! [[ ${SAFE} =~ ${file} ]]; then
    sed -i "s/_base/0/g" ${file};
    sed -i "s/^theory  */theory ${NAME}_/g" ${file};
    sed -i "s/^imports  */imports ${NAME}_/g" ${file};
    sed -i "/REMOVE_COMMENT/d" ${file};
  fi
done

cd ..

MIN=`ls ${NAME} | grep Input -v | grep "[0-9][0-9]*\.thy" -o | tr -d ".thy" | sort -n | tail -n1`
MAX=`ls ${NAME} | grep Input | grep "[0-9][0-9]*\.thy" -o  | tr -d ".thy" | sort -n | tail -n1`

for (( BASE=$MIN; BASE<$MAX; BASE++ )); do

    STEP=$[${BASE}+1]

    for file in `ls | grep "_step.thy"`; do
      file2=${NAME}/${NAME}_`echo ${file} | sed "s/_step/${STEP}/g"`
      if [[ ${SAFE} =~ ${file2} ]]; then
        cp -n ${file} ${file2};
      else
        cp ${file} ${file2};
      fi
    done

    cd ${NAME}

    for file in `ls | grep "${STEP}"`; do
      if ! [[ ${SAFE} =~ ${file} ]]; then
        sed -i "s/_base/${BASE}/g" ${file};
        sed -i "s/_step/${STEP}/g" ${file};
        sed -i "s/^theory  */theory ${NAME}_/g" ${file};
        sed -i "s/^imports  */imports ${NAME}_/g" ${file};
      fi
    done

    cd ..

done

$EDIT ${NAME}/${NAME}_Input0.thy&
