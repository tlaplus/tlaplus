/*******************************************************************************
 * Copyright (c) 2026 NVIDIA Corp. All rights reserved.
 *
 * The MIT License (MIT)
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial implementation
 ******************************************************************************/
package tlc2.mcp;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.util.HashMap;
import java.util.Map;
import java.util.stream.Collectors;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

/**
 * Handler for knowledge base resources in the MCP server.
 * 
 * Provides access to TLA+ knowledge base articles stored in docs/knowledgebase/
 * within the JAR file. Articles are markdown files with YAML frontmatter
 * containing title and description metadata.
 */
public class KnowledgeBaseResource {

	private static final String KNOWLEDGE_BASE_PATH = "/docs/knowledgebase/";
	private static final String RESOURCE_URI_PREFIX = "tlaplus://knowledge/";

	/**
	 * List of all knowledge base article filenames. These files should be in the
	 * docs/knowledgebase/ directory of the JAR.
	 */
	private static final String[] ARTICLE_FILENAMES = { "tlc-alias-expressions.md", "tla-refinement.md",
			"tla-animations.md", "tla-review-guidelines.md", "tla-functions-records-sequences.md",
			"tla-bestpractice-spec-properties.md", "tlc-trace-validation.md", "tlc-config-files.md",
			"tla-symbols-set-operations.md", "tla-stuttering.md", "tla-prove-type-correctness-lemma.md",
			"tla-pluscal.md", "tla-no-conjunct-of-invariants.md", "tla-indentation.md", "tla-functions-operators.md",
			"tla-extends-instance.md", "tla-empty-unchanged.md", "tla-different-configurations.md",
			"tla-diagnose-property-violations.md", "tla-choose-nondeterminism.md", "tla-RandomElement.md" };

	/**
	 * Metadata for a knowledge base article.
	 */
	public static class ArticleMetadata {
		public final String filename;
		public final String uri;
		public final String title;
		public final String description;

		public ArticleMetadata(String filename, String uri, String title, String description) {
			this.filename = filename;
			this.uri = uri;
			this.title = title;
			this.description = description;
		}
	}

	/**
	 * List all available knowledge base resources.
	 * 
	 * @return JSON object containing array of resource definitions
	 */
	public JsonObject listResources() {
		JsonArray resources = new JsonArray();

		for (String filename : ARTICLE_FILENAMES) {
			try {
				ArticleMetadata metadata = loadMetadata(filename);

				JsonObject resource = new JsonObject();
				resource.addProperty("uri", metadata.uri);
				resource.addProperty("name", metadata.filename);
				resource.addProperty("description", metadata.description);
				resource.addProperty("mimeType", "text/markdown");

				resources.add(resource);
			} catch (IOException e) {
				// Skip articles that can't be loaded
				System.err.println("Warning: Could not load metadata for " + filename + ": " + e.getMessage());
			}
		}

		JsonObject result = new JsonObject();
		result.add("resources", resources);
		return result;
	}

	/**
	 * Read a specific knowledge base resource.
	 * 
	 * @param uri The resource URI (e.g., "tlaplus://knowledge/tlc-config-files.md")
	 * @return JSON object containing resource content
	 * @throws IOException if the resource cannot be read
	 */
	public JsonObject readResource(String uri) throws IOException {
		if (!uri.startsWith(RESOURCE_URI_PREFIX)) {
			throw new IllegalArgumentException("Invalid resource URI: " + uri);
		}

		String filename = uri.substring(RESOURCE_URI_PREFIX.length());

		// Validate filename is in the allowed list
		boolean found = false;
		for (String allowedFile : ARTICLE_FILENAMES) {
			if (allowedFile.equals(filename)) {
				found = true;
				break;
			}
		}

		if (!found) {
			throw new IOException("Resource not found: " + uri);
		}

		// Load the article content
		ArticleContent content = loadArticleContent(filename);

		JsonObject result = new JsonObject();
		JsonArray contents = new JsonArray();

		JsonObject contentItem = new JsonObject();
		contentItem.addProperty("uri", uri);
		contentItem.addProperty("mimeType", "text/markdown");
		contentItem.addProperty("text", content.body);

		contents.add(contentItem);
		result.add("contents", contents);

		return result;
	}

	/**
	 * Load article metadata (title and description) from frontmatter.
	 */
	private ArticleMetadata loadMetadata(String filename) throws IOException {
		String resourcePath = KNOWLEDGE_BASE_PATH + filename;

		try (InputStream is = getClass().getResourceAsStream(resourcePath)) {
			if (is == null) {
				throw new IOException("Resource not found in classpath: " + resourcePath);
			}

			BufferedReader reader = new BufferedReader(new InputStreamReader(is, StandardCharsets.UTF_8));
			Map<String, String> frontmatter = parseFrontmatter(reader);

			String title = frontmatter.getOrDefault("title", filename.replace("-", " "));
			String description = frontmatter.getOrDefault("description", "");
			String uri = RESOURCE_URI_PREFIX + filename;

			return new ArticleMetadata(filename, uri, title, description);
		}
	}

	/**
	 * Load article content with frontmatter removed.
	 */
	private ArticleContent loadArticleContent(String filename) throws IOException {
		String resourcePath = KNOWLEDGE_BASE_PATH + filename;

		try (InputStream is = getClass().getResourceAsStream(resourcePath)) {
			if (is == null) {
				throw new IOException("Resource not found in classpath: " + resourcePath);
			}

			BufferedReader reader = new BufferedReader(new InputStreamReader(is, StandardCharsets.UTF_8));

			// Parse and skip frontmatter
			parseFrontmatter(reader);

			// Read the rest as the article body
			String body = reader.lines().collect(Collectors.joining("\n"));

			return new ArticleContent(body);
		}
	}

	/**
	 * Parse YAML frontmatter from a markdown file. Reads from the current position
	 * until the closing "---" delimiter. Leaves the reader positioned after the
	 * frontmatter.
	 * 
	 * @param reader BufferedReader positioned at the start of the file
	 * @return Map of frontmatter key-value pairs
	 */
	private Map<String, String> parseFrontmatter(BufferedReader reader) throws IOException {
		Map<String, String> frontmatter = new HashMap<>();

		String firstLine = reader.readLine();
		if (firstLine == null || !firstLine.trim().equals("---")) {
			// No frontmatter
			return frontmatter;
		}

		String line;
		while ((line = reader.readLine()) != null) {
			if (line.trim().equals("---")) {
				// End of frontmatter
				break;
			}

			// Parse "key: value" format
			int colonIndex = line.indexOf(':');
			if (colonIndex > 0) {
				String key = line.substring(0, colonIndex).trim();
				String value = line.substring(colonIndex + 1).trim();
				frontmatter.put(key, value);
			}
		}

		return frontmatter;
	}

	/**
	 * Container for article content.
	 */
	private static class ArticleContent {
		public final String body;

		public ArticleContent(String body) {
			this.body = body;
		}
	}
}
