package com.spbu.jmltranslator.metrics;

import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.TimeUnit;

/**
 * Класс для сбора метрик производительности трансляции
 */
public class PerformanceMetrics {
    private long startTime;
    private long endTime;
    private long memoryBefore;
    private long memoryAfter;
    private int inputTokens;
    private int outputTokens;
    private int annotationTokensBefore;
    private int annotationTokensAfter;
    private int ghostVariablesGenerated;
    private int methodsProcessed;
    private int filesProcessed;
    private Map<String, Object> additionalMetrics;
    
    public PerformanceMetrics() {
        this.additionalMetrics = new HashMap<>();
        reset();
    }
    
    public void startMeasurement() {
        this.startTime = System.nanoTime();
        this.memoryBefore = getCurrentMemoryUsage();
    }
    
    public void endMeasurement() {
        this.endTime = System.nanoTime();
        this.memoryAfter = getCurrentMemoryUsage();
    }
    
    public void setInputTokens(int tokens) {
        this.inputTokens = tokens;
    }
    
    public void setOutputTokens(int tokens) {
        this.outputTokens = tokens;
    }
    
    public void setAnnotationTokensBefore(int tokens) {
        this.annotationTokensBefore = tokens;
    }
    
    public void setAnnotationTokensAfter(int tokens) {
        this.annotationTokensAfter = tokens;
    }
    
    public void setGhostVariablesGenerated(int count) {
        this.ghostVariablesGenerated = count;
    }
    
    public void setMethodsProcessed(int count) {
        this.methodsProcessed = count;
    }
    
    public void setFilesProcessed(int count) {
        this.filesProcessed = count;
    }
    
    public int getMethodsProcessed() {
        return methodsProcessed;
    }
    
    public int getFilesProcessed() {
        return filesProcessed;
    }
    
    public void addMetric(String key, Object value) {
        this.additionalMetrics.put(key, value);
    }
    
    public long getExecutionTimeMs() {
        return TimeUnit.NANOSECONDS.toMillis(endTime - startTime);
    }
    
    public long getExecutionTimeNs() {
        return endTime - startTime;
    }
    
    public long getMemoryUsedBytes() {
        return memoryAfter - memoryBefore;
    }
    
    public long getMemoryUsedMB() {
        return getMemoryUsedBytes() / (1024 * 1024);
    }
    
    public long getTotalMemoryMB() {
        Runtime runtime = Runtime.getRuntime();
        return runtime.totalMemory() / (1024 * 1024);
    }
    
    public long getMaxMemoryMB() {
        Runtime runtime = Runtime.getRuntime();
        return runtime.maxMemory() / (1024 * 1024);
    }
    
    public double getTokensPerSecond() {
        long timeMs = getExecutionTimeMs();
        return timeMs > 0 ? (double) inputTokens / timeMs * 1000 : 0;
    }
    
    public double getExpansionRatio() {
        return inputTokens > 0 ? (double) outputTokens / inputTokens : 0;
    }
    
    public double getAnnotationExpansionRatio() {
        return annotationTokensBefore > 0 ? (double) annotationTokensAfter / annotationTokensBefore : 0;
    }
    
    public Map<String, Object> getAllMetrics() {
        Map<String, Object> metrics = new HashMap<>();
        metrics.put("executionTimeMs", getExecutionTimeMs());
        metrics.put("executionTimeNs", getExecutionTimeNs());
        metrics.put("memoryUsedBytes", getMemoryUsedBytes());
        metrics.put("memoryUsedMB", getMemoryUsedMB());
        metrics.put("totalMemoryMB", getTotalMemoryMB());
        metrics.put("maxMemoryMB", getMaxMemoryMB());
        metrics.put("inputTokens", inputTokens);
        metrics.put("outputTokens", outputTokens);
        metrics.put("annotationTokensBefore", annotationTokensBefore);
        metrics.put("annotationTokensAfter", annotationTokensAfter);
        metrics.put("ghostVariablesGenerated", ghostVariablesGenerated);
        metrics.put("methodsProcessed", methodsProcessed);
        metrics.put("filesProcessed", filesProcessed);
        metrics.put("tokensPerSecond", getTokensPerSecond());
        metrics.put("expansionRatio", getExpansionRatio());
        metrics.put("annotationExpansionRatio", getAnnotationExpansionRatio());
        metrics.putAll(additionalMetrics);
        return metrics;
    }
    
    public void reset() {
        this.startTime = 0;
        this.endTime = 0;
        this.memoryBefore = 0;
        this.memoryAfter = 0;
        this.inputTokens = 0;
        this.outputTokens = 0;
        this.annotationTokensBefore = 0;
        this.annotationTokensAfter = 0;
        this.ghostVariablesGenerated = 0;
        this.methodsProcessed = 0;
        this.filesProcessed = 0;
        this.additionalMetrics.clear();
    }
    
    private long getCurrentMemoryUsage() {
        Runtime runtime = Runtime.getRuntime();
        // Принудительно вызываем GC для более точного измерения
        System.gc();
        try {
            Thread.sleep(10); // Даём время GC завершиться
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        }
        return runtime.totalMemory() - runtime.freeMemory();
    }
    
    @Override
    public String toString() {
        return String.format(
            "PerformanceMetrics{executionTime=%dms, memoryUsed=%dMB, " +
            "inputTokens=%d, outputTokens=%d, annotationTokensBefore=%d, " +
            "annotationTokensAfter=%d, ghostVariables=%d, methods=%d, files=%d, " +
            "tokensPerSecond=%.2f, expansionRatio=%.2f, annotationExpansionRatio=%.2f}",
            getExecutionTimeMs(), getMemoryUsedMB(), inputTokens, outputTokens,
            annotationTokensBefore, annotationTokensAfter, ghostVariablesGenerated,
            methodsProcessed, filesProcessed, getTokensPerSecond(), 
            getExpansionRatio(), getAnnotationExpansionRatio()
        );
    }
} 