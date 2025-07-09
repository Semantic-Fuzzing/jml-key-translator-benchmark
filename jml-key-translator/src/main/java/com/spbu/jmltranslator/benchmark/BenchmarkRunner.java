package com.spbu.jmltranslator.benchmark;

import com.spbu.jmltranslator.JmlBatchTranslator;
import com.spbu.jmltranslator.metrics.MetricsCollector;
import com.spbu.jmltranslator.model.TranslationConfig;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

/**
 * Автоматизированный бенчмарк для тестирования производительности транслятора
 */
public class BenchmarkRunner {
    private MetricsCollector metricsCollector;
    private TranslationConfig config;
    private String outputDir;
    
    public BenchmarkRunner() {
        this.metricsCollector = new MetricsCollector();
        this.config = new TranslationConfig()
            .setGenerateGhostVars(true)
            .setHandleNullSafety(true)
            .setAddKeyLemmas(true);
    }
    
    /**
     * Запускает бенчмарк на всех тестовых файлах
     */
    public void runBenchmark(String testFilesDir, String outputDir) {
        this.outputDir = outputDir;
        
        System.out.println("=== ЗАПУСК АВТОМАТИЗИРОВАННОГО БЕНЧМАРКА ===");
        System.out.println("Тестовая директория: " + testFilesDir);
        System.out.println("Выходная директория: " + outputDir);
        System.out.println();
        
        try {
            // Получаем список всех .java файлов
            List<Path> testFiles = getTestFiles(testFilesDir);
            
            System.out.println("Найдено тестовых файлов: " + testFiles.size());
            System.out.println();
            
            // Обрабатываем каждый файл отдельно
            for (Path testFile : testFiles) {
                processSingleFile(testFile);
            }
            
            // Сохраняем отчеты
            metricsCollector.saveReports(outputDir + "/benchmark_reports");
            
            System.out.println("\n=== БЕНЧМАРК ЗАВЕРШЕН ===");
            System.out.println("Отчеты сохранены в: " + outputDir + "/benchmark_reports");
            
        } catch (Exception e) {
            System.err.println("Ошибка при выполнении бенчмарка: " + e.getMessage());
            e.printStackTrace();
        }
    }
    
    /**
     * Обрабатывает один тестовый файл с измерением метрик
     */
    private void processSingleFile(Path testFile) {
        String fileName = testFile.getFileName().toString();
        String datasetName = fileName.replace(".java", "");
        
        System.out.println("Обработка файла: " + fileName);
        
        try {
            // Читаем исходный файл
            String inputContent = Files.readString(testFile);
            
            // Начинаем измерение
            metricsCollector.startDatasetMeasurement(datasetName);
            
            // Создаем временную директорию для вывода
            Path tempOutputDir = Paths.get(outputDir, "temp_" + datasetName);
            Files.createDirectories(tempOutputDir);
            
            // Запускаем трансляцию
            String[] args = {testFile.toString(), tempOutputDir.toString()};
            JmlBatchTranslator.main(args);
            
            // Собираем результат
            StringBuilder outputContent = new StringBuilder();
            if (Files.exists(tempOutputDir)) {
                Files.walk(tempOutputDir)
                    .filter(Files::isRegularFile)
                    .filter(p -> p.toString().endsWith(".java"))
                    .forEach(outputFile -> {
                        try {
                            outputContent.append(Files.readString(outputFile)).append("\n");
                        } catch (IOException e) {
                            System.err.println("Ошибка чтения выходного файла: " + outputFile);
                        }
                    });
            }
            
            // Завершаем измерение
            metricsCollector.endDatasetMeasurement(datasetName, inputContent, outputContent.toString());
            
            // Очищаем временную директорию
            cleanupTempDirectory(tempOutputDir);
            
            System.out.println("  ✓ Успешно обработан");
            
        } catch (Exception e) {
            // Собираем метрики ошибки
            long errorTime = System.currentTimeMillis();
            metricsCollector.collectErrorMetrics(
                fileName, 
                e.getClass().getSimpleName(), 
                e.getMessage(), 
                errorTime
            );
            
            System.out.println("  ✗ Ошибка: " + e.getMessage());
        }
    }
    
    /**
     * Получает список всех тестовых файлов
     */
    private List<Path> getTestFiles(String testFilesDir) throws IOException {
        List<Path> testFiles = new ArrayList<>();
        Path testDir = Paths.get(testFilesDir);
        
        if (Files.exists(testDir)) {
            Files.walk(testDir)
                .filter(Files::isRegularFile)
                .filter(p -> p.toString().endsWith(".java"))
                .forEach(testFiles::add);
        }
        
        return testFiles;
    }
    
    /**
     * Очищает временную директорию
     */
    private void cleanupTempDirectory(Path tempDir) {
        try {
            if (Files.exists(tempDir)) {
                Files.walk(tempDir)
                    .sorted((a, b) -> b.compareTo(a)) // Сортируем в обратном порядке для удаления файлов перед директориями
                    .forEach(path -> {
                        try {
                            Files.delete(path);
                        } catch (IOException e) {
                            // Игнорируем ошибки удаления
                        }
                    });
            }
        } catch (IOException e) {
            // Игнорируем ошибки очистки
        }
    }
    
    /**
     * Запускает бенчмарк с настройками по умолчанию
     */
    public static void main(String[] args) {
        String testFilesDir = "test_files";
        String outputDir = "benchmark_output";
        
        if (args.length >= 1) {
            testFilesDir = args[0];
        }
        if (args.length >= 2) {
            outputDir = args[1];
        }
        
        BenchmarkRunner runner = new BenchmarkRunner();
        runner.runBenchmark(testFilesDir, outputDir);
    }
} 