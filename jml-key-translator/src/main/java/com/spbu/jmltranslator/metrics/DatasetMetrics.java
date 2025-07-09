package com.spbu.jmltranslator.metrics;

/**
 * Класс для хранения метрик производительности датасета
 */
public class DatasetMetrics {
    private String datasetName;
    private long executionTimeMs;
    private double memoryUsedMB;
    private int inputTokens;
    private int outputTokens;
    private int annotationTokensBefore;
    private int annotationTokensAfter;
    private int methods;
    private int fields;
    private int oldExpressions;
    private int quantifiers;
    private double tokensPerSecond;
    private double expansionRatio;
    private double annotationExpansionRatio;
    
    // Конструктор
    public DatasetMetrics() {}
    
    // Геттеры и сеттеры
    public String getDatasetName() { return datasetName; }
    public void setDatasetName(String datasetName) { this.datasetName = datasetName; }
    
    public long getExecutionTimeMs() { return executionTimeMs; }
    public void setExecutionTimeMs(long executionTimeMs) { this.executionTimeMs = executionTimeMs; }
    
    public double getMemoryUsedMB() { return memoryUsedMB; }
    public void setMemoryUsedMB(double memoryUsedMB) { this.memoryUsedMB = memoryUsedMB; }
    
    public int getInputTokens() { return inputTokens; }
    public void setInputTokens(int inputTokens) { this.inputTokens = inputTokens; }
    
    public int getOutputTokens() { return outputTokens; }
    public void setOutputTokens(int outputTokens) { this.outputTokens = outputTokens; }
    
    public int getAnnotationTokensBefore() { return annotationTokensBefore; }
    public void setAnnotationTokensBefore(int annotationTokensBefore) { this.annotationTokensBefore = annotationTokensBefore; }
    
    public int getAnnotationTokensAfter() { return annotationTokensAfter; }
    public void setAnnotationTokensAfter(int annotationTokensAfter) { this.annotationTokensAfter = annotationTokensAfter; }
    
    public int getMethods() { return methods; }
    public void setMethods(int methods) { this.methods = methods; }
    
    public int getFields() { return fields; }
    public void setFields(int fields) { this.fields = fields; }
    
    public int getOldExpressions() { return oldExpressions; }
    public void setOldExpressions(int oldExpressions) { this.oldExpressions = oldExpressions; }
    
    public int getQuantifiers() { return quantifiers; }
    public void setQuantifiers(int quantifiers) { this.quantifiers = quantifiers; }
    
    public double getTokensPerSecond() { return tokensPerSecond; }
    public void setTokensPerSecond(double tokensPerSecond) { this.tokensPerSecond = tokensPerSecond; }
    
    public double getExpansionRatio() { return expansionRatio; }
    public void setExpansionRatio(double expansionRatio) { this.expansionRatio = expansionRatio; }
    
    public double getAnnotationExpansionRatio() { return annotationExpansionRatio; }
    public void setAnnotationExpansionRatio(double annotationExpansionRatio) { this.annotationExpansionRatio = annotationExpansionRatio; }
    
    @Override
    public String toString() {
        return String.format(
            "DatasetMetrics{datasetName='%s', executionTime=%dms, memoryUsed=%.2fMB, " +
            "inputTokens=%d, outputTokens=%d, annotationTokensBefore=%d, annotationTokensAfter=%d, " +
            "methods=%d, fields=%d, oldExpressions=%d, quantifiers=%d, " +
            "tokensPerSecond=%.2f, expansionRatio=%.2f, annotationExpansionRatio=%.2f}",
            datasetName, executionTimeMs, memoryUsedMB, inputTokens, outputTokens,
            annotationTokensBefore, annotationTokensAfter, methods, fields, oldExpressions, quantifiers,
            tokensPerSecond, expansionRatio, annotationExpansionRatio
        );
    }
} 