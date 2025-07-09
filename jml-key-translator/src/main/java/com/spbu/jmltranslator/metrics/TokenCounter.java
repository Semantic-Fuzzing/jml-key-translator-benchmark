package com.spbu.jmltranslator.metrics;

import java.util.regex.Pattern;

/**
 * Класс для подсчета токенов в Java и JML коде
 */
public class TokenCounter {
    
    // Паттерны для различных типов токенов
    private static final Pattern WHITESPACE_PATTERN = Pattern.compile("\\s+");
    private static final Pattern COMMENT_PATTERN = Pattern.compile("//.*$|/\\*.*?\\*/", Pattern.MULTILINE | Pattern.DOTALL);
    private static final Pattern JML_ANNOTATION_PATTERN = Pattern.compile("//@.*$", Pattern.MULTILINE);
    private static final Pattern STRING_LITERAL_PATTERN = Pattern.compile("\"[^\"]*\"");
    private static final Pattern CHAR_LITERAL_PATTERN = Pattern.compile("'[^']'");
    private static final Pattern NUMBER_PATTERN = Pattern.compile("\\b\\d+(\\.\\d+)?\\b");
    private static final Pattern IDENTIFIER_PATTERN = Pattern.compile("\\b[a-zA-Z_][a-zA-Z0-9_]*\\b");
    private static final Pattern OPERATOR_PATTERN = Pattern.compile("[+\\-*/%=<>!&|^~]+");
    private static final Pattern PUNCTUATION_PATTERN = Pattern.compile("[{}()\\[\\];,.]");
    
    /**
     * Подсчитывает общее количество токенов в коде
     */
    public static int countTotalTokens(String code) {
        if (code == null || code.trim().isEmpty()) {
            return 0;
        }
        
        // Удаляем обычные комментарии, но НЕ JML-аннотации
        String cleanCode = code;
        
        // Удаляем многострочные комментарии /* ... */
        cleanCode = cleanCode.replaceAll("/\\*.*?\\*/", " ");
        
        // Удаляем однострочные комментарии //, но НЕ //@
        String[] lines = cleanCode.split("\n");
        StringBuilder processedCode = new StringBuilder();
        
        for (String line : lines) {
            String processedLine = line;
            // Удаляем комментарии //, но сохраняем //@
            int commentIndex = processedLine.indexOf("//");
            if (commentIndex >= 0) {
                // Проверяем, не является ли это JML-аннотацией
                if (commentIndex + 2 < processedLine.length() && processedLine.charAt(commentIndex + 2) == '@') {
                    // Это JML-аннотация, оставляем как есть
                    processedCode.append(processedLine).append("\n");
                } else {
                    // Это обычный комментарий, удаляем
                    processedCode.append(processedLine.substring(0, commentIndex)).append("\n");
                }
            } else {
                processedCode.append(processedLine).append("\n");
            }
        }
        
        cleanCode = processedCode.toString();
        
        // Разбиваем на токены по пробелам и другим разделителям
        String[] tokens = WHITESPACE_PATTERN.split(cleanCode);
        
        int count = 0;
        for (String token : tokens) {
            if (!token.trim().isEmpty()) {
                count += countTokenComplexity(token);
            }
        }
        
        return count;
    }
    
    /**
     * Подсчитывает токены только в JML аннотациях
     */
    public static int countJmlAnnotationTokens(String code) {
        if (code == null || code.trim().isEmpty()) {
            return 0;
        }
        
        int totalTokens = 0;
        String[] lines = code.split("\n");
        
        for (String line : lines) {
            if (line.trim().startsWith("//@")) {
                // Удаляем "//@" и считаем остальные токены
                String annotationContent = line.substring(line.indexOf("//@") + 3);
                totalTokens += countTotalTokens(annotationContent);
            }
        }
        
        return totalTokens;
    }
    
    /**
     * Подсчитывает количество JML аннотаций
     */
    public static int countJmlAnnotations(String code) {
        if (code == null || code.trim().isEmpty()) {
            return 0;
        }
        
        int count = 0;
        String[] lines = code.split("\n");
        
        for (String line : lines) {
            if (line.trim().startsWith("//@")) {
                count++;
            }
        }
        
        return count;
    }
    
    /**
     * Подсчитывает количество методов в коде
     */
    public static int countMethods(String code) {
        if (code == null || code.trim().isEmpty()) {
            return 0;
        }
        
        // Простой паттерн для поиска методов
        Pattern methodPattern = Pattern.compile(
            "\\s*(?:public|protected|private|static)?\\s*[\\w<>\\[\\]]+\\s+\\w+\\s*\\([^)]*\\)\\s*\\{"
        );
        
        java.util.regex.Matcher matcher = methodPattern.matcher(code);
        int count = 0;
        while (matcher.find()) {
            count++;
        }
        
        return count;
    }
    
    /**
     * Подсчитывает количество полей класса
     */
    public static int countFields(String code) {
        if (code == null || code.trim().isEmpty()) {
            return 0;
        }
        
        // Паттерн для поиска полей класса
        Pattern fieldPattern = Pattern.compile(
            "\\s*(?:private|protected|public)\\s+[\\w<>\\[\\]]+\\s+\\w+\\s*;"
        );
        
        java.util.regex.Matcher matcher = fieldPattern.matcher(code);
        int count = 0;
        while (matcher.find()) {
            count++;
        }
        
        return count;
    }
    
    /**
     * Подсчитывает количество \old() выражений
     */
    public static int countOldExpressions(String code) {
        if (code == null || code.trim().isEmpty()) {
            return 0;
        }
        
        Pattern oldPattern = Pattern.compile("\\\\old\\s*\\(");
        java.util.regex.Matcher matcher = oldPattern.matcher(code);
        int count = 0;
        while (matcher.find()) {
            count++;
        }
        
        return count;
    }
    
    /**
     * Подсчитывает количество кванторов (forall, exists)
     */
    public static int countQuantifiers(String code) {
        if (code == null || code.trim().isEmpty()) {
            return 0;
        }
        
        Pattern quantifierPattern = Pattern.compile("\\\\(?:forall|exists)\\s+");
        java.util.regex.Matcher matcher = quantifierPattern.matcher(code);
        int count = 0;
        while (matcher.find()) {
            count++;
        }
        
        return count;
    }
    
    /**
     * Подсчитывает сложность отдельного токена
     */
    private static int countTokenComplexity(String token) {
        if (token == null || token.trim().isEmpty()) {
            return 0;
        }
        
        // Строковые литералы считаем как один токен
        if (STRING_LITERAL_PATTERN.matcher(token).matches()) {
            return 1;
        }
        
        // Символьные литералы
        if (CHAR_LITERAL_PATTERN.matcher(token).matches()) {
            return 1;
        }
        
        // Числа
        if (NUMBER_PATTERN.matcher(token).matches()) {
            return 1;
        }
        
        // Identifiers
        if (IDENTIFIER_PATTERN.matcher(token).matches()) {
            return 1;
        }
        
        // Operators
        if (OPERATOR_PATTERN.matcher(token).matches()) {
            return 1;
        }
        
        // Punctuation
        if (PUNCTUATION_PATTERN.matcher(token).matches()) {
            return 1;
        }
        
        // For complex tokens, split further
        return token.length();
    }
    
    /**
     * Получает детальную статистику по токенам
     */
    public static TokenStatistics getDetailedStatistics(String code) {
        TokenStatistics stats = new TokenStatistics();
        
        if (code == null || code.trim().isEmpty()) {
            return stats;
        }
        
        stats.setTotalTokens(countTotalTokens(code));
        stats.setJmlAnnotationTokens(countJmlAnnotationTokens(code));
        stats.setJmlAnnotations(countJmlAnnotations(code));
        stats.setMethods(countMethods(code));
        stats.setFields(countFields(code));
        stats.setOldExpressions(countOldExpressions(code));
        stats.setQuantifiers(countQuantifiers(code));
        
        return stats;
    }
    
    /**
     * Внутренний класс для хранения статистики токенов
     */
    public static class TokenStatistics {
        private int totalTokens;
        private int jmlAnnotationTokens;
        private int jmlAnnotations;
        private int methods;
        private int fields;
        private int oldExpressions;
        private int quantifiers;
        
        // Геттеры и сеттеры
        public int getTotalTokens() { return totalTokens; }
        public void setTotalTokens(int totalTokens) { this.totalTokens = totalTokens; }
        
        public int getJmlAnnotationTokens() { return jmlAnnotationTokens; }
        public void setJmlAnnotationTokens(int jmlAnnotationTokens) { this.jmlAnnotationTokens = jmlAnnotationTokens; }
        
        public int getJmlAnnotations() { return jmlAnnotations; }
        public void setJmlAnnotations(int jmlAnnotations) { this.jmlAnnotations = jmlAnnotations; }
        
        public int getMethods() { return methods; }
        public void setMethods(int methods) { this.methods = methods; }
        
        public int getFields() { return fields; }
        public void setFields(int fields) { this.fields = fields; }
        
        public int getOldExpressions() { return oldExpressions; }
        public void setOldExpressions(int oldExpressions) { this.oldExpressions = oldExpressions; }
        
        public int getQuantifiers() { return quantifiers; }
        public void setQuantifiers(int quantifiers) { this.quantifiers = quantifiers; }
        
        @Override
        public String toString() {
            return String.format(
                "TokenStatistics{totalTokens=%d, jmlAnnotationTokens=%d, jmlAnnotations=%d, " +
                "methods=%d, fields=%d, oldExpressions=%d, quantifiers=%d}",
                totalTokens, jmlAnnotationTokens, jmlAnnotations, methods, fields, oldExpressions, quantifiers
            );
        }
    }
} 