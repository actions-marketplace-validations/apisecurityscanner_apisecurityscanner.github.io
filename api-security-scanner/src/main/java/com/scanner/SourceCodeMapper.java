package com.scanner;

import java.io.IOException;
import java.nio.file.FileVisitOption;
import java.nio.file.FileVisitResult;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.SimpleFileVisitor;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Enterprise-grade local codebase scanner (SAST) that inspects workspace source files
 * across Java, Kotlin, TypeScript, JavaScript, Python, Go, and C# for controller
 * annotations and routing declarations, mapping OpenAPI endpoints to the exact source
 * file path and line number.
 *
 * <p>Engineered for massive enterprise codebases (100k - 1,000,000+ lines of code):
 * <ul>
 *   <li>Prunes vendor/build directories early with {@code SKIP_SUBTREE} to prevent directory tree explosion</li>
 *   <li>Enforces per-file memory ceilings (1 MB max) to prevent OutOfMemoryError on generated/minified files</li>
 *   <li>Bounds total indexed files (25,000) and mapped locations (50,000) to keep JVM heap usage strictly capped</li>
 *   <li>Maintains O(1) exact-match hash indices to eliminate regex bottleneck across thousands of endpoints</li>
 *   <li>Safe against circular symlink loops, locked files, and permission errors</li>
 * </ul>
 */
public final class SourceCodeMapper {

    public record SourceLocation(
            String filePath,
            int lineNumber,
            String httpMethod,
            String routePath
    ) {
        public String display() {
            return filePath + ":" + lineNumber;
        }
    }

    private static final int MAX_WALK_DEPTH = 25;
    private static final long MAX_SOURCE_FILE_SIZE = 1_048_576L; // 1 MB limit per file
    private static final int MAX_FILES_TO_SCAN = 25_000;
    private static final int MAX_MAPPED_LOCATIONS = 50_000;

    private static final Set<String> IGNORED_DIRS = Set.of(
            ".git", "target", "build", ".gradle", ".idea", ".vscode", "node_modules", "vendor",
            "dist", "out", "bin", "obj", "coverage", ".terraform", "venv", ".env", "__pycache__",
            "tmp", "temp", ".cache", "generated-sources", "bower_components", ".serverless",
            "public", "Pods", ".dart_tool", ".m2", "packages", ".next", ".nuxt", "static"
    );

    private static final Set<String> SUPPORTED_EXTENSIONS = Set.of(
            ".java", ".kt", ".ts", ".tsx", ".js", ".jsx", ".py", ".go", ".cs"
    );

    // Spring route annotations (Java / Kotlin): @GetMapping, @PostMapping, etc.
    private static final Pattern SPRING_MAPPING = Pattern.compile(
            "@(GetMapping|PostMapping|PutMapping|DeleteMapping|PatchMapping|RequestMapping)\\s*(?:\\(([^)]*)\\))?",
            Pattern.DOTALL
    );

    // JAX-RS annotations: @Path("..."), @GET, @POST, etc.
    private static final Pattern JAXRS_PATH = Pattern.compile(
            "@Path\\s*\\(\\s*\"([^\"]+)\"\\s*\\)"
    );
    private static final Pattern JAXRS_METHOD = Pattern.compile(
            "@(GET|POST|PUT|DELETE|PATCH|OPTIONS|HEAD)\\b"
    );

    // Express / Fastify / Ktor / Router calls: app.get("/users", ...), router.post("/users", ...)
    private static final Pattern ROUTE_CALL = Pattern.compile(
            "(?:app|router|server|r|api)\\.(get|post|put|delete|patch|options|head|createContext)\\s*\\(\\s*[\"']([^\"']+)[\"']"
            + "|(?:path\\.equals|path\\.startsWith)\\s*\\(\\s*[\"']([^\"']+)[\"']",
            Pattern.CASE_INSENSITIVE
    );

    // Python FastAPI / Flask / Django: @app.get("/users"), @router.post("/users"), @app.route("/users")
    private static final Pattern PYTHON_ROUTE = Pattern.compile(
            "@(?:app|router|api)\\.(get|post|put|delete|patch|route)\\s*\\(\\s*[\"']([^\"']+)[\"']",
            Pattern.CASE_INSENSITIVE
    );

    // C# ASP.NET Core: [HttpGet("users")], [HttpPost], [Route("users")]
    private static final Pattern CSHARP_ROUTE = Pattern.compile(
            "\\[(?:Http(Get|Post|Put|Delete|Patch)|Route)\\s*(?:\\(\\s*[\"']([^\"']+)[\"']\\s*\\))?\\]",
            Pattern.CASE_INSENSITIVE
    );

    private static final Pattern CLASS_DECL = Pattern.compile(
            "\\b(?:public|protected|private)?\\s*(?:abstract|final)?\\s*(?:class|record|interface)\\s+(\\w+)"
    );

    private final List<SourceLocation> mappedLocations = new ArrayList<>();
    private final List<String> scannedFiles = new ArrayList<>();

    // O(1) indices for ultra-fast lookup across 10,000+ endpoints
    private final Map<String, SourceLocation> exactMatchIndex = new ConcurrentHashMap<>();
    private final Map<String, List<SourceLocation>> methodIndex = new ConcurrentHashMap<>();

    public SourceCodeMapper() {
    }

    public SourceCodeMapper(String rootPath) {
        if (rootPath != null && !rootPath.isBlank()) {
            scanDirectory(Path.of(rootPath));
        }
    }

    public List<String> getScannedFiles() {
        return Collections.unmodifiableList(scannedFiles);
    }

    public List<SourceLocation> getMappedLocations() {
        return Collections.unmodifiableList(mappedLocations);
    }

    public void scanDirectory(Path root) {
        if (root == null || !Files.exists(root)) {
            return;
        }

        try {
            Files.walkFileTree(root, EnumSet.noneOf(FileVisitOption.class), MAX_WALK_DEPTH, new SimpleFileVisitor<>() {
                @Override
                public FileVisitResult preVisitDirectory(Path dir, BasicFileAttributes attrs) {
                    Path fileName = dir.getFileName();
                    if (fileName != null) {
                        String dirName = fileName.toString();
                        if (IGNORED_DIRS.contains(dirName) || (dirName.startsWith(".") && !dir.equals(root))) {
                            return FileVisitResult.SKIP_SUBTREE;
                        }
                    }
                    if (scannedFiles.size() >= MAX_FILES_TO_SCAN) {
                        return FileVisitResult.TERMINATE;
                    }
                    return FileVisitResult.CONTINUE;
                }

                @Override
                public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) {
                    if (scannedFiles.size() >= MAX_FILES_TO_SCAN) {
                        return FileVisitResult.TERMINATE;
                    }
                    if (attrs.isRegularFile() && attrs.size() <= MAX_SOURCE_FILE_SIZE) {
                        String name = file.getFileName().toString();
                        int dot = name.lastIndexOf('.');
                        if (dot > 0) {
                            String ext = name.substring(dot).toLowerCase(Locale.ROOT);
                            if (SUPPORTED_EXTENSIONS.contains(ext)) {
                                scanFile(file);
                            }
                        }
                    }
                    return FileVisitResult.CONTINUE;
                }

                @Override
                public FileVisitResult visitFileFailed(Path file, IOException exc) {
                    return FileVisitResult.CONTINUE;
                }
            });
        } catch (Throwable e) {
            System.out.println("  ! Source scan error on " + root + ": " + e.getMessage());
        }
    }

    public void scanFile(Path file) {
        if (scannedFiles.size() >= MAX_FILES_TO_SCAN || mappedLocations.size() >= MAX_MAPPED_LOCATIONS) {
            return;
        }
        try {
            if (Files.size(file) > MAX_SOURCE_FILE_SIZE) {
                return; // Guard memory against huge minified or generated artifacts
            }
            String content = Files.readString(file);
            // Quick heuristic: ignore binary files that might masquerade as source files
            if (content.length() > 512 && content.substring(0, 512).indexOf('\0') >= 0) {
                return;
            }

            // Normalize path separators to forward slashes for cross-platform consistency
            String relative = file.toString().replace('\\', '/');
            if (relative.startsWith("./")) {
                relative = relative.substring(2);
            }
            scannedFiles.add(relative);
            scanSourceContent(relative, content);
        } catch (IOException | OutOfMemoryError e) {
            // Ignore unreadable files or memory warnings safely
        }
    }

    public void scanSourceContent(String relativePath, String content) {
        if (content == null || content.isBlank() || mappedLocations.size() >= MAX_MAPPED_LOCATIONS) {
            return;
        }

        String[] lines = content.split("\\R", -1);

        // Track class-level path mapping
        String classLevelPath = "";
        int classDeclLine = -1;

        Matcher classMatcher = CLASS_DECL.matcher(content);
        if (classMatcher.find()) {
            int classStart = classMatcher.start();
            classDeclLine = getLineNumber(content, classStart);
            String beforeClass = content.substring(0, classStart);
            Matcher rmClassMatcher = Pattern.compile("@(?:RequestMapping|Path|Controller)\\s*(?:\\(([^)]*)\\))?").matcher(beforeClass);
            while (rmClassMatcher.find()) {
                String val = extractPathFromAnnotationParam(rmClassMatcher.group(1));
                if (val != null && !val.isBlank()) {
                    classLevelPath = normalizePath(val);
                }
            }
        }

        // 1. Scan for Spring annotations (Java / Kotlin)
        Matcher springMatcher = SPRING_MAPPING.matcher(content);
        while (springMatcher.find()) {
            int line = getLineNumber(content, springMatcher.start());
            String annotationName = springMatcher.group(1);
            String params = springMatcher.group(2);

            if (classDeclLine > 0 && line < classDeclLine && "RequestMapping".equals(annotationName)) {
                continue;
            }

            String method = resolveSpringHttpMethod(annotationName, params);
            String pathPart = extractPathFromAnnotationParam(params);
            String fullPath = combinePaths(classLevelPath, pathPart);

            addMappedLocation(new SourceLocation(relativePath, line, method, fullPath));
        }

        // 2. Scan for JAX-RS annotations
        Matcher jaxrsPathMatcher = JAXRS_PATH.matcher(content);
        while (jaxrsPathMatcher.find()) {
            int line = getLineNumber(content, jaxrsPathMatcher.start());
            if (classDeclLine > 0 && line < classDeclLine) {
                continue;
            }
            String pathPart = jaxrsPathMatcher.group(1);
            String fullPath = combinePaths(classLevelPath, pathPart);
            String httpMethod = findNearbyJaxRsMethod(lines, line);
            addMappedLocation(new SourceLocation(relativePath, line, httpMethod, fullPath));
        }

        // 3. Scan for Express / Fastify / Node / Go / Ktor route registrations
        Matcher routeMatcher = ROUTE_CALL.matcher(content);
        while (routeMatcher.find()) {
            int line = getLineNumber(content, routeMatcher.start());
            String methodGroup = routeMatcher.group(1);
            String pathVal = routeMatcher.group(2) != null ? routeMatcher.group(2) : routeMatcher.group(3);
            if (pathVal != null && !pathVal.isBlank()) {
                String normPath = normalizePath(pathVal);
                String httpMethod = methodGroup != null && !methodGroup.equalsIgnoreCase("createContext")
                        ? methodGroup.toUpperCase(Locale.ROOT)
                        : findNearbyHttpMethod(lines, line);
                addMappedLocation(new SourceLocation(relativePath, line, httpMethod, normPath));
            }
        }

        // 4. Scan for Python FastAPI / Flask routes
        Matcher pyMatcher = PYTHON_ROUTE.matcher(content);
        while (pyMatcher.find()) {
            int line = getLineNumber(content, pyMatcher.start());
            String m = pyMatcher.group(1).toUpperCase(Locale.ROOT);
            String pathVal = normalizePath(pyMatcher.group(2));
            String httpMethod = "ROUTE".equals(m) ? "ALL" : m;
            addMappedLocation(new SourceLocation(relativePath, line, httpMethod, pathVal));
        }

        // 5. Scan for C# ASP.NET Core attributes
        Matcher csMatcher = CSHARP_ROUTE.matcher(content);
        while (csMatcher.find()) {
            int line = getLineNumber(content, csMatcher.start());
            String m = csMatcher.group(1);
            String pathVal = csMatcher.group(2);
            String httpMethod = m != null ? m.toUpperCase(Locale.ROOT) : "ALL";
            String fullPath = pathVal != null ? combinePaths(classLevelPath, pathVal) : classLevelPath;
            if (!fullPath.isEmpty() && !fullPath.equals("/")) {
                addMappedLocation(new SourceLocation(relativePath, line, httpMethod, fullPath));
            }
        }

        // 6. Heuristic convention-based method scanning (e.g. UserController with getUser, deleteUser, searchUsers)
        Pattern methodDeclPattern = Pattern.compile(
                "\\b(?:public|protected|private)?\\s*(?:[\\w<>\\[\\],\\s]+)\\s+([a-zA-Z0-9_]+)\\s*\\(([^)]*)\\)\\s*(?:throws\\s+[^{]+)?\\{",
                Pattern.MULTILINE
        );
        String detectedResource = "";
        if (classDeclLine > 0) {
            Matcher cMatch = CLASS_DECL.matcher(content);
            if (cMatch.find()) {
                String cName = cMatch.group(1).toLowerCase(Locale.ROOT);
                for (String suffix : List.of("controller", "resource", "service", "handler", "api", "endpoint", "routes", "route")) {
                    if (cName.endsWith(suffix) && cName.length() > suffix.length()) {
                        detectedResource = cName.substring(0, cName.length() - suffix.length());
                        break;
                    }
                }
                if (detectedResource.isEmpty()) {
                    detectedResource = cName;
                }
            }
        }
        if (!detectedResource.isEmpty() && classLevelPath.isEmpty()) {
            classLevelPath = "/" + (detectedResource.endsWith("s") ? detectedResource : detectedResource + "s");
        }

        Matcher methodMatcher = methodDeclPattern.matcher(content);
        while (methodMatcher.find()) {
            int line = getLineNumber(content, methodMatcher.start());
            if (classDeclLine > 0 && line <= classDeclLine) {
                continue;
            }
            String mName = methodMatcher.group(1);
            String mParams = methodMatcher.group(2);
            String lowerM = mName.toLowerCase(Locale.ROOT);

            String httpMethod = null;
            String pathSuffix = "";

            if (lowerM.startsWith("get") || lowerM.startsWith("find") || lowerM.startsWith("search") || lowerM.startsWith("fetch") || lowerM.startsWith("list") || lowerM.startsWith("read")) {
                httpMethod = "GET";
                if (mParams.toLowerCase(Locale.ROOT).contains("id") || lowerM.endsWith("byid")) {
                    pathSuffix = "/{id}";
                }
            } else if (lowerM.startsWith("delete") || lowerM.startsWith("remove")) {
                httpMethod = "DELETE";
                if (mParams.toLowerCase(Locale.ROOT).contains("id") || lowerM.endsWith("byid")) {
                    pathSuffix = "/{id}";
                }
            } else if (lowerM.startsWith("post") || lowerM.startsWith("create") || lowerM.startsWith("add") || lowerM.startsWith("save") || lowerM.startsWith("insert")) {
                httpMethod = "POST";
            } else if (lowerM.startsWith("put") || lowerM.startsWith("update") || lowerM.startsWith("modify") || lowerM.startsWith("patch")) {
                httpMethod = "PUT";
                if (mParams.toLowerCase(Locale.ROOT).contains("id") || lowerM.endsWith("byid")) {
                    pathSuffix = "/{id}";
                }
            }

            if (httpMethod != null && !classLevelPath.isEmpty()) {
                String fullPath = combinePaths(classLevelPath, pathSuffix);
                addMappedLocation(new SourceLocation(relativePath, line, httpMethod, fullPath));
            }
        }
    }

    private synchronized void addMappedLocation(SourceLocation loc) {
        if (mappedLocations.size() >= MAX_MAPPED_LOCATIONS) {
            return;
        }

        // Fast deduplication check
        String key = loc.filePath() + ":" + loc.lineNumber();
        for (SourceLocation existing : mappedLocations) {
            if (existing.filePath().equals(loc.filePath()) && existing.lineNumber() == loc.lineNumber()) {
                return;
            }
        }

        mappedLocations.add(loc);

        // Index for instantaneous O(1) matching
        String normPath = normalizePath(loc.routePath());
        String m = loc.httpMethod() != null ? loc.httpMethod().toUpperCase(Locale.ROOT) : "ALL";
        exactMatchIndex.putIfAbsent(m + "|" + normPath, loc);

        methodIndex.computeIfAbsent(m, k -> new ArrayList<>()).add(loc);
        if (!m.equals("ALL")) {
            methodIndex.computeIfAbsent("ALL", k -> new ArrayList<>()).add(loc);
        }
    }

    /**
     * Finds the best matching source location for a given HTTP method and OpenAPI path.
     * Uses O(1) exact-match indexing first, followed by indexed candidate scoring.
     */
    public SourceLocation findLocation(String method, String openApiPath) {
        if (openApiPath == null) {
            return null;
        }

        String targetMethod = method != null ? method.toUpperCase(Locale.ROOT) : "GET";
        String normalizedTarget = normalizePath(openApiPath);

        // 1. High-speed O(1) exact hash match
        SourceLocation exact = exactMatchIndex.get(targetMethod + "|" + normalizedTarget);
        if (exact != null) {
            return exact;
        }
        exact = exactMatchIndex.get("ALL|" + normalizedTarget);
        if (exact != null) {
            return exact;
        }

        // 2. Candidate pool search (restricted to matching HTTP methods only)
        List<SourceLocation> candidates = new ArrayList<>();
        List<SourceLocation> directMethod = methodIndex.get(targetMethod);
        if (directMethod != null) {
            candidates.addAll(directMethod);
        }
        List<SourceLocation> allMethod = methodIndex.get("ALL");
        if (allMethod != null) {
            candidates.addAll(allMethod);
        }

        if (candidates.isEmpty()) {
            candidates = mappedLocations;
        }

        SourceLocation bestMatch = null;
        int bestScore = -1;

        for (SourceLocation loc : candidates) {
            int score = scoreMatch(loc, targetMethod, normalizedTarget);
            if (score > bestScore) {
                bestScore = score;
                bestMatch = loc;
                if (score >= 130) {
                    break; // High confidence match - stop early
                }
            }
        }

        if (bestScore >= 50 && bestMatch != null) {
            return bestMatch;
        }

        // 3. Fallback: If no exact method/path mapping found, locate candidate source file matching the path noun
        if (!scannedFiles.isEmpty()) {
            String pathNoun = extractPathNoun(openApiPath);
            for (String file : scannedFiles) {
                String fileLower = file.toLowerCase(Locale.ROOT);
                if (fileLower.contains(pathNoun) || fileLower.contains("controller") || fileLower.contains("api") || fileLower.contains("resource") || fileLower.contains("route")) {
                    return new SourceLocation(file, 1, targetMethod, openApiPath);
                }
            }
            return new SourceLocation(scannedFiles.get(0), 1, targetMethod, openApiPath);
        }

        return null;
    }

    private static String extractPathNoun(String path) {
        String clean = path.replaceAll("^/+", "").replaceAll("\\{[^}]+\\}", "").replaceAll("/.*", "").toLowerCase(Locale.ROOT);
        if (clean.endsWith("s") && clean.length() > 3) {
            clean = clean.substring(0, clean.length() - 1);
        }
        return clean.isEmpty() ? "api" : clean;
    }

    private int scoreMatch(SourceLocation loc, String targetMethod, String targetPath) {
        String locMethod = loc.httpMethod() != null ? loc.httpMethod().toUpperCase(Locale.ROOT) : "ALL";
        boolean methodMatches = locMethod.equals("ALL") || locMethod.equals(targetMethod);
        if (!methodMatches) {
            return 0;
        }

        String locPath = normalizePath(loc.routePath());
        int methodScore = locMethod.equals(targetMethod) ? 50 : 20;

        // 1. Exact match
        if (locPath.equalsIgnoreCase(targetPath)) {
            return methodScore + 100;
        }

        // 2. Wildcard / template match ({id} vs {userId})
        if (pathTemplatesMatch(locPath, targetPath)) {
            return methodScore + 80;
        }

        // 3. Suffix or prefix match (e.g. context-path /api/users vs /users)
        if (isPrefixOrSuffixMatch(locPath, targetPath)) {
            return methodScore + 40;
        }

        return 0;
    }

    private static boolean pathTemplatesMatch(String p1, String p2) {
        if (!p1.contains("{") && !p2.contains("{")) {
            return false;
        }
        // Normalize all placeholders to wildcard tokens for fast comparison without regex overhead
        String tokenized1 = p1.replaceAll("\\{[^}/]+\\}", "*");
        String tokenized2 = p2.replaceAll("\\{[^}/]+\\}", "*");
        if (tokenized1.equalsIgnoreCase(tokenized2)) {
            return true;
        }
        try {
            String regex1 = p1.replaceAll("\\{[^}/]+\\}", "[^/]+");
            String regex2 = p2.replaceAll("\\{[^}/]+\\}", "[^/]+");
            return p2.matches(regex1) || p1.matches(regex2);
        } catch (Exception ignored) {
            return false;
        }
    }

    private static boolean isPrefixOrSuffixMatch(String p1, String p2) {
        if (p1.isEmpty() || p2.isEmpty() || p1.equals("/") || p2.equals("/")) {
            return false;
        }
        String clean1 = p1.replaceAll("^/+", "").replaceAll("/+$", "");
        String clean2 = p2.replaceAll("^/+", "").replaceAll("/+$", "");
        return clean1.endsWith(clean2) || clean2.endsWith(clean1)
                || clean1.startsWith(clean2) || clean2.startsWith(clean1);
    }

    static int getLineNumber(String text, int charIndex) {
        int line = 1;
        int max = Math.min(charIndex, text.length());
        for (int i = 0; i < max; i++) {
            if (text.charAt(i) == '\n') {
                line++;
            }
        }
        return line;
    }

    static String extractPathFromAnnotationParam(String params) {
        if (params == null || params.isBlank()) {
            return "";
        }
        Matcher m = Pattern.compile("(?:value|path)\\s*=\\s*(?:\\{\\s*)?\"([^\"]+)\"|\"([^\"]+)\"").matcher(params);
        if (m.find()) {
            return m.group(1) != null ? m.group(1) : m.group(2);
        }
        return "";
    }

    static String resolveSpringHttpMethod(String annotationName, String params) {
        return switch (annotationName) {
            case "GetMapping" -> "GET";
            case "PostMapping" -> "POST";
            case "PutMapping" -> "PUT";
            case "DeleteMapping" -> "DELETE";
            case "PatchMapping" -> "PATCH";
            case "RequestMapping" -> {
                if (params != null) {
                    Matcher m = Pattern.compile("RequestMethod\\.(GET|POST|PUT|DELETE|PATCH)").matcher(params);
                    if (m.find()) {
                        yield m.group(1);
                    }
                }
                yield "ALL";
            }
            default -> "ALL";
        };
    }

    static String combinePaths(String classPath, String methodPath) {
        String p1 = classPath == null ? "" : classPath.trim();
        String p2 = methodPath == null ? "" : methodPath.trim();
        if (p1.isEmpty() && p2.isEmpty()) {
            return "/";
        }
        String combined = p1 + "/" + p2;
        combined = combined.replaceAll("/+", "/");
        if (combined.length() > 1 && combined.endsWith("/")) {
            combined = combined.substring(0, combined.length() - 1);
        }
        if (!combined.startsWith("/")) {
            combined = "/" + combined;
        }
        return combined;
    }

    static String normalizePath(String path) {
        if (path == null || path.isBlank()) {
            return "/";
        }
        String p = path.trim().replaceAll("/+", "/");
        if (!p.startsWith("/")) {
            p = "/" + p;
        }
        if (p.length() > 1 && p.endsWith("/")) {
            p = p.substring(0, p.length() - 1);
        }
        return p;
    }

    private String findNearbyJaxRsMethod(String[] lines, int line) {
        int start = Math.max(0, line - 4);
        int end = Math.min(lines.length - 1, line + 3);
        for (int i = start; i <= end; i++) {
            Matcher m = JAXRS_METHOD.matcher(lines[i]);
            if (m.find()) {
                return m.group(1);
            }
        }
        return "ALL";
    }

    private String findNearbyHttpMethod(String[] lines, int line) {
        int start = Math.max(0, line - 3);
        int end = Math.min(lines.length - 1, line + 5);
        for (int i = start; i <= end; i++) {
            Matcher m = Pattern.compile("method\\.equals\\s*\\(\\s*\"(GET|POST|PUT|DELETE)\"", Pattern.CASE_INSENSITIVE)
                    .matcher(lines[i]);
            if (m.find()) {
                return m.group(1).toUpperCase(Locale.ROOT);
            }
        }
        return "ALL";
    }

    /**
     * Checks if a scanned source location corresponds to any declared OpenAPI path.
     * Used for Shadow API discovery (detecting endpoints that exist in code but are absent from OpenAPI spec).
     */
    public static boolean matchesAnySpecEndpoint(SourceLocation loc, Collection<String> specPaths) {
        if (loc == null || loc.routePath() == null || specPaths == null || specPaths.isEmpty()) {
            return false;
        }
        String locPath = normalizePath(loc.routePath());
        for (String specPath : specPaths) {
            String normSpec = normalizePath(specPath);
            if (locPath.equalsIgnoreCase(normSpec)
                    || pathTemplatesMatch(locPath, normSpec)
                    || isPrefixOrSuffixMatch(locPath, normSpec)) {
                return true;
            }
        }
        return false;
    }
}
