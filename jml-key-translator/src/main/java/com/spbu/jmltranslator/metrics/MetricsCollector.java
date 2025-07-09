package com.spbu.jmltranslator.metrics;

import com.spbu.jmltranslator.model.JmlMethod;
import com.spbu.jmltranslator.translator.AnnotationHandler;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * Класс для автоматического сбора метрик во время трансляции
 */
public class MetricsCollector {
    private PerformanceMetrics performanceMetrics;
    private List<DatasetMetrics> datasetMetrics;
    private List<ErrorMetrics> errorMetrics;
    
    public MetricsCollector() {
        this.performanceMetrics = new PerformanceMetrics();
        this.datasetMetrics = new ArrayList<>();
        this.errorMetrics = new ArrayList<>();
    }
    
    /**
     * Начинает сбор метрик для нового датасета
     */
    public void startDatasetMeasurement(String datasetName) {
        performanceMetrics.startMeasurement();
    }
    
    /**
     * Завершает сбор метрик для датасета
     */
    public void endDatasetMeasurement(String datasetName, String inputContent, String outputContent) {
        performanceMetrics.endMeasurement();
        
        // Собираем статистику токенов
        TokenCounter.TokenStatistics inputStats = TokenCounter.getDetailedStatistics(inputContent);
        TokenCounter.TokenStatistics outputStats = TokenCounter.getDetailedStatistics(outputContent);
        
        // Обновляем метрики производительности
        performanceMetrics.setInputTokens(inputStats.getTotalTokens());
        performanceMetrics.setOutputTokens(outputStats.getTotalTokens());
        performanceMetrics.setAnnotationTokensBefore(inputStats.getJmlAnnotationTokens());
        performanceMetrics.setAnnotationTokensAfter(outputStats.getJmlAnnotationTokens());
        
        // Создаем метрики датасета
        DatasetMetrics datasetMetric = new DatasetMetrics();
        datasetMetric.setDatasetName(datasetName);
        datasetMetric.setExecutionTimeMs(performanceMetrics.getExecutionTimeMs());
        datasetMetric.setMemoryUsedMB(performanceMetrics.getMemoryUsedMB());
        datasetMetric.setInputTokens(inputStats.getTotalTokens());
        datasetMetric.setOutputTokens(outputStats.getTotalTokens());
        datasetMetric.setAnnotationTokensBefore(inputStats.getJmlAnnotationTokens());
        datasetMetric.setAnnotationTokensAfter(outputStats.getJmlAnnotationTokens());
        datasetMetric.setMethods(inputStats.getMethods());
        datasetMetric.setFields(inputStats.getFields());
        datasetMetric.setOldExpressions(inputStats.getOldExpressions());
        datasetMetric.setQuantifiers(inputStats.getQuantifiers());
        datasetMetric.setTokensPerSecond(performanceMetrics.getTokensPerSecond());
        datasetMetric.setExpansionRatio(performanceMetrics.getExpansionRatio());
        datasetMetric.setAnnotationExpansionRatio(performanceMetrics.getAnnotationExpansionRatio());
        
        datasetMetrics.add(datasetMetric);
        
        // Сбрасываем метрики для следующего измерения
        performanceMetrics.reset();
    }
    
    /**
     * Собирает метрики для отдельного метода
     */
    public void collectMethodMetrics(JmlMethod method, AnnotationHandler annotationHandler) {
        // Подсчитываем ghost-переменные
        int ghostVars = annotationHandler.getGhostVariables().size();
        performanceMetrics.setGhostVariablesGenerated(ghostVars);
        
        // Увеличиваем счетчик методов
        performanceMetrics.setMethodsProcessed(performanceMetrics.getMethodsProcessed() + 1);
    }
    
    /**
     * Собирает метрики ошибок
     */
    public void collectErrorMetrics(String fileName, String errorType, String errorMessage, long executionTimeMs) {
        ErrorMetrics errorMetric = new ErrorMetrics();
        errorMetric.setFileName(fileName);
        errorMetric.setErrorType(errorType);
        errorMetric.setErrorMessage(errorMessage);
        errorMetric.setExecutionTimeMs(executionTimeMs);
        
        errorMetrics.add(errorMetric);
    }
    
    /**
     * Увеличивает счетчик обработанных файлов
     */
    public void incrementFilesProcessed() {
        performanceMetrics.setFilesProcessed(performanceMetrics.getFilesProcessed() + 1);
    }
    
    /**
     * Генерирует отчет в формате CSV для датасетов
     */
    public String generateDatasetReport() {
        StringBuilder report = new StringBuilder();
        
        // Заголовок
        report.append("Dataset,ExecutionTime(ms),MemoryUsed(MB),InputTokens,OutputTokens,")
              .append("AnnotationTokensBefore,AnnotationTokensAfter,Methods,Fields,OldExpressions,")
              .append("Quantifiers,TokensPerSecond,ExpansionRatio,AnnotationExpansionRatio\n");
        
        // Данные
        for (DatasetMetrics metric : datasetMetrics) {
            report.append(String.format("%s,%d,%.2f,%d,%d,%d,%d,%d,%d,%d,%d,%.2f,%.2f,%.2f\n",
                metric.getDatasetName(),
                metric.getExecutionTimeMs(),
                metric.getMemoryUsedMB(),
                metric.getInputTokens(),
                metric.getOutputTokens(),
                metric.getAnnotationTokensBefore(),
                metric.getAnnotationTokensAfter(),
                metric.getMethods(),
                metric.getFields(),
                metric.getOldExpressions(),
                metric.getQuantifiers(),
                metric.getTokensPerSecond(),
                metric.getExpansionRatio(),
                metric.getAnnotationExpansionRatio()
            ));
        }
        
        return report.toString();
    }
    
    /**
     * Генерирует отчет в формате CSV для ошибок
     */
    public String generateErrorReport() {
        StringBuilder report = new StringBuilder();
        
        // Заголовок
        report.append("FileName,ErrorType,ErrorMessage,ExecutionTime(ms)\n");
        
        // Данные
        for (ErrorMetrics metric : errorMetrics) {
            report.append(String.format("%s,%s,%s,%d\n",
                metric.getFileName(),
                metric.getErrorType(),
                metric.getErrorMessage().replace(",", ";"), // Заменяем запятые для CSV
                metric.getExecutionTimeMs()
            ));
        }
        
        return report.toString();
    }
    
    /**
     * Генерирует сводный отчет
     */
    public String generateSummaryReport() {
        StringBuilder report = new StringBuilder();
        
        report.append("=== СВОДНЫЙ ОТЧЕТ ПО ПРОИЗВОДИТЕЛЬНОСТИ ===\n\n");
        
        // Общая статистика
        report.append("ОБЩАЯ СТАТИСТИКА:\n");
        report.append(String.format("Всего обработано датасетов: %d\n", datasetMetrics.size()));
        report.append(String.format("Всего ошибок: %d\n", errorMetrics.size()));
        
        if (!datasetMetrics.isEmpty()) {
            // Средние значения
            double avgExecutionTime = datasetMetrics.stream()
                .mapToLong(DatasetMetrics::getExecutionTimeMs)
                .average().orElse(0.0);
            
            double avgMemoryUsed = datasetMetrics.stream()
                .mapToDouble(DatasetMetrics::getMemoryUsedMB)
                .average().orElse(0.0);
            
            double avgTokensPerSecond = datasetMetrics.stream()
                .mapToDouble(DatasetMetrics::getTokensPerSecond)
                .average().orElse(0.0);
            
            report.append(String.format("Среднее время выполнения: %.2f мс\n", avgExecutionTime));
            report.append(String.format("Среднее использование памяти: %.2f МБ\n", avgMemoryUsed));
            report.append(String.format("Средняя скорость обработки: %.2f токенов/сек\n", avgTokensPerSecond));
        }
        
        // Топ-5 самых медленных датасетов
        if (datasetMetrics.size() > 1) {
            report.append("\nТОП-5 САМЫХ МЕДЛЕННЫХ ДАТАСЕТОВ:\n");
            datasetMetrics.stream()
                .sorted((a, b) -> Long.compare(b.getExecutionTimeMs(), a.getExecutionTimeMs()))
                .limit(5)
                .forEach(metric -> report.append(String.format("- %s: %d мс\n", 
                    metric.getDatasetName(), metric.getExecutionTimeMs())));
        }
        
        // Статистика ошибок
        if (!errorMetrics.isEmpty()) {
            report.append("\nСТАТИСТИКА ОШИБОК:\n");
            Map<String, Long> errorTypeCounts = errorMetrics.stream()
                .collect(java.util.stream.Collectors.groupingBy(
                    ErrorMetrics::getErrorType, 
                    java.util.stream.Collectors.counting()));
            
            errorTypeCounts.forEach((type, count) -> 
                report.append(String.format("- %s: %d\n", type, count)));
        }
        
        return report.toString();
    }
    
    /**
     * Сохраняет отчеты в файлы
     */
    public void saveReports(String outputDir) {
        try {
            java.nio.file.Path outputPath = java.nio.file.Paths.get(outputDir);
            java.nio.file.Files.createDirectories(outputPath);
            
            // Сохраняем отчет по датасетам
            java.nio.file.Files.writeString(
                outputPath.resolve("dataset_metrics.csv"), 
                generateDatasetReport()
            );
            
            // Сохраняем отчет по ошибкам
            java.nio.file.Files.writeString(
                outputPath.resolve("error_metrics.csv"), 
                generateErrorReport()
            );
            
            // Сохраняем сводный отчет
            java.nio.file.Files.writeString(
                outputPath.resolve("summary_report.txt"), 
                generateSummaryReport()
            );
            
            System.out.println("Отчеты сохранены в директорию: " + outputDir);
            
        } catch (Exception e) {
            System.err.println("Ошибка при сохранении отчетов: " + e.getMessage());
        }
    }
    
    // Геттеры
    public PerformanceMetrics getPerformanceMetrics() { return performanceMetrics; }
    public List<DatasetMetrics> getDatasetMetrics() { return datasetMetrics; }
    public List<ErrorMetrics> getErrorMetrics() { return errorMetrics; }
} 