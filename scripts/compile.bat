@echo off
echo Компиляция JML транслятора с UTF-8 кодировкой...

cd jml-key-translator

echo Создание папки target/classes...
if not exist target\classes mkdir target\classes

echo Компиляция основных классов...
javac -encoding UTF-8 -d target/classes src/main/java/com/spbu/jmltranslator/JmlKeyTranslator.java src/main/java/com/spbu/jmltranslator/JmlBatchTranslator.java

echo Компиляция модели...
javac -encoding UTF-8 -d target/classes src/main/java/com/spbu/jmltranslator/model/*.java

echo Компиляция fileio...
javac -encoding UTF-8 -d target/classes src/main/java/com/spbu/jmltranslator/fileio/*.java

echo Компиляция translator...
javac -encoding UTF-8 -d target/classes src/main/java/com/spbu/jmltranslator/translator/*.java

echo Компиляция metrics...
javac -encoding UTF-8 -d target/classes src/main/java/com/spbu/jmltranslator/metrics/*.java

echo Компиляция benchmark...
javac -encoding UTF-8 -d target/classes src/main/java/com/spbu/jmltranslator/benchmark/*.java

echo Компиляция завершена!
cd ..

pause 