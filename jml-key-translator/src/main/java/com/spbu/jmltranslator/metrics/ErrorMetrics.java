package com.spbu.jmltranslator.metrics;

/**
 * Класс для хранения метрик ошибок
 */
public class ErrorMetrics {
    private String fileName;
    private String errorType;
    private String errorMessage;
    private long executionTimeMs;
    
    // Конструктор
    public ErrorMetrics() {}
    
    // Геттеры и сеттеры
    public String getFileName() { return fileName; }
    public void setFileName(String fileName) { this.fileName = fileName; }
    
    public String getErrorType() { return errorType; }
    public void setErrorType(String errorType) { this.errorType = errorType; }
    
    public String getErrorMessage() { return errorMessage; }
    public void setErrorMessage(String errorMessage) { this.errorMessage = errorMessage; }
    
    public long getExecutionTimeMs() { return executionTimeMs; }
    public void setExecutionTimeMs(long executionTimeMs) { this.executionTimeMs = executionTimeMs; }
    
    @Override
    public String toString() {
        return String.format(
            "ErrorMetrics{fileName='%s', errorType='%s', errorMessage='%s', executionTime=%dms}",
            fileName, errorType, errorMessage, executionTimeMs
        );
    }
} 