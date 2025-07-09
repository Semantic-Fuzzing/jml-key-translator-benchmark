# Система автоматического сбора метрик производительности JML транслятора

## Описание

Данная система автоматически собирает метрики производительности транслятора JML в Key на известных датасетах и генерирует подробные отчеты.

## Структура проекта

```
summer/
├── build/                         # Артефакты сборки
├── config/                        # Конфигурационные файлы
├── docs/                          # Документация
├── examples/                      # Примеры использования
│   ├── input/                     # Входные тестовые файлы
│   └── output/                    # Выходные файлы
├── jml-key-translator/            # Основной проект
├── logs/                          # Логи
├── reports/                       # Отчеты и результаты
│   ├── benchmark_output/          # Результаты бенчмарков
│   │   └── benchmark_reports/     # CSV и текстовые отчёты
│   ├── comparison_metrics.txt     # Метрики сравнения
│   ├── input_test_metrics.txt     # Метрики входных файлов
│   └── testing_comparison_report.txt # Сравнительный отчет
├── scripts/                       # Скрипты
├── temp/                          # Временные файлы (.class)
└── tools/                         # Инструменты разработки
    ├── analysis/                  # Анализ и метрики
    ├── debugging/                 # Отладка
    └── testing/                   # Тестирование
```

## Собираемые метрики

### 1. Метрики производительности
- **Время выполнения** (мс)
- **Использование памяти** (МБ)
- **Скорость обработки** (токенов/сек)

### 2. Метрики нагрузки (токены)
- **Входные токены** - общее количество токенов в исходном коде
- **Выходные токены** - общее количество токенов в трансформированном коде
- **Токены аннотаций ДО** - количество токенов в JML аннотациях до трансляции
- **Токены аннотаций ПОСЛЕ** - количество токенов в JML аннотациях после трансляции

### 3. Метрики сложности кода
- **Количество методов**
- **Количество полей**
- **Количество \old() выражений**
- **Количество кванторов**
- **Количество ghost-переменных**

### 4. Метрики расширения
- **Коэффициент расширения** (выходные токены / входные токены)
- **Коэффициент расширения аннотаций** (токены аннотаций после / токены аннотаций до)

### 5. Метрики ошибок
- **Тип ошибки**
- **Сообщение об ошибке**
- **Время выполнения до ошибки**

## Запуск бенчмарка

### Windows
```bash
run_benchmark.bat
```

### Linux/Mac
```bash
chmod +x run_benchmark.sh
./run_benchmark.sh
```

### Ручной запуск
```bash
cd jml-key-translator
javac -encoding UTF-8 -d target src/main/java/com/spbu/jmltranslator/model/*.java
javac -encoding UTF-8 -cp target -d target src/main/java/com/spbu/jmltranslator/translator/*.java
javac -encoding UTF-8 -cp target -d target src/main/java/com/spbu/jmltranslator/fileio/*.java
javac -encoding UTF-8 -cp target -d target src/main/java/com/spbu/jmltranslator/metrics/*.java
javac -encoding UTF-8 -cp target -d target src/main/java/com/spbu/jmltranslator/benchmark/*.java
javac -encoding UTF-8 -cp target -d target src/main/java/com/spbu/jmltranslator/*.java
cd ..
java -cp jml-key-translator/target com.spbu.jmltranslator.benchmark.BenchmarkRunner examples/input reports/benchmark_output
```

## Генерируемые отчеты

После выполнения бенчмарка в папке `reports/benchmark_output/benchmark_reports/` создаются следующие файлы:

### 1. dataset_metrics.csv
Таблица с характеристиками трансляции на всех датасетах:
```csv
Dataset,ExecutionTime(ms),MemoryUsed(MB),InputTokens,OutputTokens,AnnotationTokensBefore,AnnotationTokensAfter,Methods,Fields,OldExpressions,Quantifiers,TokensPerSecond,ExpansionRatio,AnnotationExpansionRatio
Account,15,2.5,45,67,12,18,1,1,1,0,3000.0,1.49,1.50
MaxBad,12,1.8,38,52,8,14,1,0,0,0,3166.7,1.37,1.75
...
```

### 2. error_metrics.csv
Таблица со скоростью всех ошибок для софта с ошибками:
```csv
FileName,ErrorType,ErrorMessage,ExecutionTime(ms)
BrokenFile.java,IOException,File not found,5
InvalidSyntax.java,ParseException,Invalid JML syntax,8
...
```

### 3. summary_report.txt
Сводный отчет с общей статистикой:
```
=== СВОДНЫЙ ОТЧЕТ ПО ПРОИЗВОДИТЕЛЬНОСТИ ===

ОБЩАЯ СТАТИСТИКА:
Всего обработано датасетов: 8
Всего ошибок: 0
Среднее время выполнения: 24,00 мс
Среднее использование памяти: 0,38 МБ
Средняя скорость обработки: 20,699 токенов/сек

Топ-5 самых медленных датасетов:
  1. Account: 119 мс
  2. MaxByElimination: 18 мс
  3. Max: 17 мс
  4. ArrayHelper: 13 мс
  5. PositiveAccount: 8 мс
```

## Примеры использования

### Анализ производительности
```java
// Создание коллектора метрик
MetricsCollector collector = new MetricsCollector();

// Начало измерения
collector.startDatasetMeasurement("MyDataset");

// Выполнение трансляции
// ... код трансляции ...

// Завершение измерения
collector.endDatasetMeasurement("MyDataset", inputContent, outputContent);

// Получение отчета
String report = collector.generateDatasetReport();
```

### Подсчет токенов
```java
// Подсчет общих токенов
int totalTokens = TokenCounter.countTotalTokens(javaCode);

// Подсчет токенов в JML аннотациях
int annotationTokens = TokenCounter.countJmlAnnotationTokens(javaCode);
```

## Инструменты анализа

### InputTestMetrics
Анализирует входные файлы и создает отчет с метриками:
```bash
java -cp "jml-key-translator/target;tools/analysis" tools.analysis.InputTestMetrics
```

### ComparisonMetrics
Сравнивает входные и выходные файлы:
```bash
java -cp "jml-key-translator/target;tools/analysis" tools.analysis.ComparisonMetrics
```

### CountTest
Тестирует подсчет токенов:
```bash
java -cp "jml-key-translator/target;tools/testing" tools.testing.CountTest
```

### TokenDebug
Отлаживает подсчет токенов:
```bash
java -cp "jml-key-translator/target;tools/debugging" tools.debugging.TokenDebug
```

## Интерпретация результатов

### Коэффициенты расширения
- **ExpansionRatio > 1.0**: Код расширяется при трансляции
- **ExpansionRatio ≈ 1.0**: Код остается примерно того же размера
- **ExpansionRatio < 1.0**: Код сжимается при трансляции

### Скорость обработки
- **> 5000 токенов/сек**: Отличная производительность
- **1000-5000 токенов/сек**: Хорошая производительность
- **< 1000 токенов/сек**: Требует оптимизации

### Использование памяти
- **< 5 МБ**: Низкое потребление
- **5-20 МБ**: Среднее потребление
- **> 20 МБ**: Высокое потребление

## Требования

- Java 11 или выше
- Доступ к файловой системе для чтения/записи
- Минимум 100 МБ свободной памяти для больших датасетов

## Устранение неполадок

### Ошибки компиляции
- Убедитесь, что все зависимости на месте
- Проверьте версию Java (должна быть 11+)
- Используйте правильную кодировку UTF-8 при компиляции

### Ошибки выполнения
- Проверьте права доступа к файлам
- Убедитесь, что тестовые файлы существуют в examples/input
- Проверьте свободное место на диске

### Неточные метрики
- Закройте другие приложения для точного измерения памяти
- Запускайте бенчмарк несколько раз для усреднения результатов
- Используйте одинаковые условия для всех тестов 