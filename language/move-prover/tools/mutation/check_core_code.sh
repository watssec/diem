folder="../../../../diem-move/diem-framework/core/sources"
for file in $(ls $folder);
do
  . ~/.profile
  cargo run -- ../../../../swap/src/modules/module.move -d ../../../../language/move-stdlib/sources -d $folder
done