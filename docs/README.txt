JML Key Translator
====================

JML Key Translator — инструмент для трансляции JML-аннотаций в Java-код, пригодный для верификации в KeY. Поддерживает обработку как отдельных файлов, так и целых директорий, а также автоматизированный сбор метрик производительности и генерацию подробных отчётов.

Структура проекта:
------------------

summer/
├── build/                         # Артефакты сборки
├── config/                        # Конфигурационные файлы
├── docs/                          # Документация
│   ├── README.txt                 # Основная документация
│   ├── BENCHMARK_README.md        # Руководство по бенчмаркам
│   └── тестирование.txt           # Отчет о тестировании
├── examples/                      # Примеры использования
│   ├── input/                     # Входные тестовые файлы
│   │   ├── Account.java
│   │   ├── ArrayHelper.java
│   │   ├── Max.java
│   │   ├── MaxBad.java
│   │   ├── MaxByElimination.java
│   │   ├── MaxByEliminationBad.java
│   │   ├── PositiveAccount.java
│   │   └── SafeDivider.java
│   └── output/                    # Выходные файлы (разделенные по методам)
│       ├── Account_deposit.java
│       ├── ArrayHelper_allPositive.java
│       ├── ArrayHelper_findMax.java
│       ├── MaxBad_max.java
│       ├── MaxByEliminationBad_max.java
│       ├── MaxByElimination_max.java
│       ├── Max_max.java
│       ├── PositiveAccount_add.java
│       ├── PositiveAccount_getValue.java
│       ├── SafeDivider_divide.java
│       └── SafeDivider_factorial.java
├── jml-key-translator/            # Основной проект
│   ├── src/main/java/com/spbu/jmltranslator/
│   │   ├── JmlKeyTranslator.java         # Трансляция одного файла
│   │   ├── JmlBatchTranslator.java       # Пакетная трансляция
│   │   ├── benchmark/                    # Автоматизированный бенчмарк
│   │   ├── metrics/                      # Метрики и отчёты
│   │   ├── fileio/                       # Работа с файлами и директориями
│   │   ├── model/                        # Модели данных
│   │   ├── translator/                   # Логика трансляции
│   │   └── resources/config.properties   # Конфигурация
│   └── target/classes/                   # Скомпилированные классы
├── logs/                          # Логи (готово для будущего использования)
├── reports/                       # Отчеты и результаты
│   ├── benchmark_output/          # Результаты бенчмарков
│   │   └── benchmark_reports/     # CSV и текстовые отчёты
│   ├── comparison_metrics.txt     # Метрики сравнения
│   ├── input_test_metrics.txt     # Метрики входных файлов
│   └── testing_comparison_report.txt # Сравнительный отчет
├── scripts/                       # Скрипты (готово для compile.bat)
├── temp/                          # Временные файлы (.class)
└── tools/                         # Инструменты разработки
    ├── analysis/                  # Анализ и метрики
    │   ├── ComparisonMetrics.java # Сравнение метрик
    │   └── InputTestMetrics.java  # Метрики входных файлов
    ├── debugging/                 # Отладка
    │   ├── memory_test.java       # Тест памяти JVM
    │   └── TokenDebug.java        # Отладка токенов
    └── testing/                   # Тестирование
        └── CountTest.java         # Тест подсчета токенов

Требования:
-----------
- Java 11 или новее (JDK)
- PowerShell (Windows) или bash (Linux/Mac)

Сборка и запуск проекта
=======================

1. Перейдите в папку jml-key-translator:
   cd jml-key-translator

2. Скомпилируйте проект поэтапно (Windows PowerShell):
   javac -encoding UTF-8 -d target src/main/java/com/spbu/jmltranslator/model/*.java
   javac -encoding UTF-8 -cp target -d target src/main/java/com/spbu/jmltranslator/translator/*.java
   javac -encoding UTF-8 -cp target -d target src/main/java/com/spbu/jmltranslator/fileio/*.java
   javac -encoding UTF-8 -cp target -d target src/main/java/com/spbu/jmltranslator/metrics/*.java
   javac -encoding UTF-8 -cp target -d target src/main/java/com/spbu/jmltranslator/benchmark/*.java
   javac -encoding UTF-8 -cp target -d target src/main/java/com/spbu/jmltranslator/*.java

3. Перейдите в корень проекта:
   cd ..

4. Запустите транслятор или бенчмарк:
   - Для трансляции одного файла:
     java -cp jml-key-translator/target com.spbu.jmltranslator.JmlKeyTranslator examples/input/Account.java output/Account_key.java
   - Для пакетной трансляции:
     java -cp jml-key-translator/target com.spbu.jmltranslator.JmlBatchTranslator examples/input output_test
   - Для автоматизированного бенчмарка:
     java -cp jml-key-translator/target com.spbu.jmltranslator.benchmark.BenchmarkRunner

5. Запустите инструменты анализа:
   - Анализ входных файлов:
     java -cp "jml-key-translator/target;tools/analysis" tools.analysis.InputTestMetrics
   - Сравнение входных и выходных файлов:
     java -cp "jml-key-translator/target;tools/analysis" tools.analysis.ComparisonMetrics
   - Тест подсчета токенов:
     java -cp "jml-key-translator/target;tools/testing" tools.testing.CountTest
   - Отладка токенов:
     java -cp "jml-key-translator/target;tools/debugging" tools.debugging.TokenDebug
   - Тест памяти:
     java -cp tools/debugging tools.debugging.memory_test

Результаты:
-----------
- В папке output_test появятся файлы для методов с JML-аннотациями.
- В папке reports/ будут отчёты:
  - benchmark_output/benchmark_reports/ — результаты бенчмарков
  - comparison_metrics.txt — метрики сравнения
  - input_test_metrics.txt — метрики входных файлов
  - testing_comparison_report.txt — сравнительный отчет

Автоматизированный бенчмарк и метрики:
--------------------------------------
- Система автоматически собирает:
  - Время выполнения и использование памяти
  - Количество токенов до/после трансляции
  - Количество методов, полей, кванторов, old-выражений
  - Скорость обработки (токенов/сек)
  - Коэффициенты расширения аннотаций
- Все метрики сохраняются в CSV и текстовых отчётах для анализа.

Инструменты разработки:
-----------------------
- **tools/analysis/** — инструменты для анализа метрик и сравнения файлов
- **tools/testing/** — инструменты для тестирования функциональности
- **tools/debugging/** — инструменты для отладки и диагностики

FAQ:
----
- **Где взять тестовые файлы?**
  — Положите свои Java-файлы с JML-аннотациями в папку examples/input.
- **Как изменить параметры?**
  — Отредактируйте config.properties в jml-key-translator/src/main/java/com/spbu/jmltranslator/resources/.
- **Что делать, если не запускается?**
  — Проверьте, что все классы скомпилированы, и пути к файлам указаны правильно.
- **Как добавить новые тесты?**
  — Просто добавьте новые .java-файлы в examples/input и перезапустите транслятор или бенчмарк.
- **Как использовать инструменты анализа?**
  — Перейдите в соответствующую папку tools/ и запустите нужный инструмент с правильным classpath.

Контакты:
---------
Если возникли вопросы по работе транслятора или интеграции с KeY, пишите в Issues на GitHub или напрямую автору: lylyca326@gmail.com

---
Если нужно добавить описание опций, примеры аннотаций или расширить FAQ — напишите, и README будет дополнен. 