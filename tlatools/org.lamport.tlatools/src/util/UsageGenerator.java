package util;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * A helper class to print usage text for a command-line-application in a motif reminiscent of manpages.
 *  
 * In a world where we were not concerned with jar size, i would import Apache Commons CLI and take advantage
 * 	of those classes.
 */
public class UsageGenerator {
	private static final String NAME = "NAME";
	private static final String SYNOPSIS = "SYNOPSIS";
	private static final String DESCRIPTION = "DESCRIPTION";
	private static final String OPTIONS = "OPTIONS";
	private static final String TIPS = "TIPS";
	
	private static Comparator<Argument> NAME_COMPARATOR = new Comparator<Argument>() {
		@Override
		public int compare(final Argument a, final Argument b) {
			return a.getArgumentName().compareTo(b.getArgumentName());
		}
	};
	
	private static Comparator<Argument> NAME_DASH_COMPARATOR = new Comparator<Argument>() {
		@Override
		public int compare(final Argument a, final Argument b) {
			final boolean aDash = a.isDashArgument();
			final boolean bDash = b.isDashArgument();
			
			if (aDash != bDash) {
				return aDash ? -1 : 1;
			}
			
			return a.getArgumentName().compareTo(b.getArgumentName());
		}
	};
	
	
	public static void displayUsage(final PrintStream ps, final String commandName, final String version,
									final String commandShortSummary, final String commandDescription,
									final List<List<Argument>> commandVariants, final List<String> tips,
									final char valuedArgumentsSeparator) {
		ps.println();
		ps.println(generateSectionHeader(NAME));
		ps.println('\t' + commandName + " - " + commandShortSummary
						+ ((version != null) ? (" - " + version) : "") + "\n\n");

		
		final String boldName = markupWord(commandName, true);
		
		
		final HashSet<Argument> arguments = new HashSet<>();
		ps.println(generateSectionHeader(SYNOPSIS));
		for (final List<Argument> variant : commandVariants) {
			ps.println("\t" + generateCommandForVariant(boldName, variant, arguments, valuedArgumentsSeparator));
		}
		ps.println();
		
		
		final String commandNameRegex = commandName + "(\\)|\\s|$)";
		final Pattern p = Pattern.compile(commandNameRegex);
		final Matcher m = p.matcher(commandDescription);
		final String markedUpDescription;
		if (m.find()) {
			final StringBuilder sb = new StringBuilder();
			
			if (m.start() > 0) {
				sb.append(commandDescription.substring(0, m.start()));
			}
			sb.append(boldName).append(m.group(1));
			
			int lastEnd = m.end();
			while (m.find()) {
				sb.append(commandDescription.substring(lastEnd, m.start())).append(boldName).append(m.group(1));
				lastEnd = m.end();
			}
			sb.append(commandDescription.substring(lastEnd, commandDescription.length()));
			
			markedUpDescription = sb.toString();
		} else {
			markedUpDescription = commandDescription;
		}
		
		ps.println(generateSectionHeader(DESCRIPTION));
		ps.println("\t" + markedUpDescription.replaceAll("(\\r\\n|\\r|\\n)", "\n\t"));
		ps.println();
		
		
		final List<Argument> orderedArguments = new ArrayList<>(arguments);
		Collections.sort(orderedArguments, NAME_COMPARATOR);
		ps.println(generateSectionHeader(OPTIONS));
		for (final Argument arg : orderedArguments) {
			if (arg.expectsValue() || arg.isOptional() || (!arg.expectsValue() && arg.isDashArgument())) {
				ps.println(generateOptionText(arg, valuedArgumentsSeparator));
			}
		}
		ps.println();
		
		
		if ((tips != null) && (tips.size() > 0)) {
			ps.println(generateSectionHeader(TIPS));
			for (final String tip : tips) {
				ps.println("\t" + tip.replaceAll("(\\r\\n|\\r|\\n)", "\n\t") + "\n");
			}
		}
	}
	
	private static String generateCommandForVariant(final String boldedCommandName, final List<Argument> variant,
													final HashSet<Argument> arguments,
													final char valuedArgumentsSeparator) {
		final List<Argument> optionalSingleDashValueless = new ArrayList<>();
		final List<Argument> optionalDoubleDashValueless = new ArrayList<>();
		final List<Argument> optionalValued = new ArrayList<>();
		final List<Argument> requiredValued = new ArrayList<>();
		final List<Argument> requiredValueless = new ArrayList<>();
		
		for (final Argument arg : variant) {
			if (arg.expectsValue()) {
				if (arg.isOptional()) {
					optionalValued.add(arg);
				} else {
					requiredValued.add(arg);
				}
			} else {
				if (arg.isOptional()) {
					if (arg.isDashArgument()) {
						optionalSingleDashValueless.add(arg);
					} else if (arg.isDashDashArgument()) {
						optionalDoubleDashValueless.add(arg);
					}
				} else {
					requiredValueless.add(arg);
				}
			}
		}

		Collections.sort(optionalSingleDashValueless, NAME_COMPARATOR);
		Collections.sort(optionalDoubleDashValueless, NAME_COMPARATOR);
		Collections.sort(optionalValued, NAME_COMPARATOR);
		Collections.sort(requiredValued, NAME_COMPARATOR);
		Collections.sort(requiredValueless, NAME_DASH_COMPARATOR);

		final StringBuilder sb = new StringBuilder(boldedCommandName);
		
		if (optionalSingleDashValueless.size() > 0) {
			final StringBuilder concatenation = new StringBuilder("-");
			final List<Argument> nonShortArguments = new ArrayList<>();
			for (final Argument arg : optionalSingleDashValueless) {
				if (arg.isShortArgument()) {
					concatenation.append(arg.getDashlessArgumentName());
				} else {
					nonShortArguments.add(arg);
				}
			}
			if (concatenation.length() > 1) {
				sb.append(" [").append(markupWord(concatenation.toString(), true)).append(']');
			}
			
			for (final Argument arg : nonShortArguments) {
				sb.append(" [").append(markupWord(("-" + arg.getDashlessArgumentName()), true));
				if (arg.hasSubOptions()) {
					sb.append(" [").append(arg.getSubOptions()).append("]");
				}
				sb.append(']');
			}
		}
		
		if (optionalDoubleDashValueless.size() > 0) {
			for (final Argument arg : optionalDoubleDashValueless) {
				sb.append(" [").append(markupWord(arg.getArgumentName(), true));
				if (arg.hasSubOptions()) {
					sb.append(" [").append(arg.getSubOptions()).append("]");
				}
				sb.append(']');
			}
		}
		
		if (optionalValued.size() > 0) {
			for (final Argument arg : optionalValued) {
				sb.append(" [").append(markupWord(arg.getArgumentName(), true)).append(valuedArgumentsSeparator);
				if (arg.hasSubOptions()) {
					sb.append("[").append(arg.getSubOptions()).append("] ");
				}
				sb.append(markupWord(arg.getSampleValue(), false)).append(']');
			}
		}
		
		if (requiredValued.size() > 0) {
			for (final Argument arg : requiredValued) {
				sb.append(" ").append(markupWord(arg.getArgumentName(), true)).append(valuedArgumentsSeparator);
				sb.append(markupWord(arg.getSampleValue(), false));
			}
		}
		
		if (requiredValueless.size() > 0) {
			for (final Argument arg : requiredValueless) {
				sb.append(" ").append(arg.getArgumentName());
				if (arg.hasSubOptions()) {
					sb.append(" [").append(arg.getSubOptions()).append("]");
				}
			}
		}
		
		arguments.addAll(variant);
		
		return sb.toString();
	}
	
	private static String generateOptionText(final Argument argument, final char valuedArgumentsSeparator) {
		final StringBuilder sb = new StringBuilder("\t");

		sb.append(markupWord(argument.getArgumentName(), true));
		if (argument.expectsValue()) {
			sb.append(valuedArgumentsSeparator).append(markupWord(argument.getSampleValue(), false));
		}
		sb.append("\n\t\t").append(argument.getDescription().replaceAll("(\\r\\n|\\r|\\n)", "\n\t\t"));

		return sb.toString();
	}
		
	private static String generateSectionHeader(final String title) {
		final StringBuilder sb = new StringBuilder(markupWord(title, true));
		
		sb.append('\n');
		
		return sb.toString();
	}
	
	/**
	 * @param bold if true, the word will be bolded; false, the word will be italicized
	 */
	private static String markupWord(final String word, final boolean bold) {
		final StringBuilder sb = new StringBuilder(bold ? TLAConstants.ANSI.BOLD_CODE : TLAConstants.ANSI.ITALIC_CODE);
		
		sb.append(word).append(TLAConstants.ANSI.RESET_CODE);
		
		return sb.toString();
	}
	
	
	public static class Argument {
		private final String argumentName;
		private final String sampleValue;
		private final String description;
		private final boolean optional;
		private final String subOptions;
		
		/**
		 * This calls {@code this(key, optionDescription, false);}
		 * 
		 * @param key
		 * @param optionDescription
		 */
		public Argument(final String key, final String optionDescription) {
			this(key, optionDescription, false);
		}
		
		public Argument(final String key, final String optionDescription, final boolean isOptional) {
			this(key, null, optionDescription, isOptional);
		}
		
		/**
		 * This calls {@code this(key, exampleValue, optionDescription, false);}
		 */
		public Argument(final String key, final String exampleValue, final String optionDescription) {
			this(key, exampleValue, optionDescription, false);
		}
		
		public Argument(final String key, final String exampleValue, final String optionDescription,
						final boolean isOptional) {
			this(key, exampleValue, optionDescription, isOptional, null);
		}
		
		public Argument(final String key, final String exampleValue, final String optionDescription,
						final boolean isOptional, final String concatenatedSuboptions) {
			argumentName = key;
			sampleValue = exampleValue;
			description = optionDescription;
			optional = isOptional;
			subOptions = concatenatedSuboptions;
		}
		
		public boolean isOptional() {
			return optional;
		}
		
		public boolean expectsValue() {
			return (sampleValue != null);
		}
		
		/**
		 * @return if the argument name starts with "-", but not "--", this returns true
		 */
		public boolean isDashArgument() {
			return argumentName.startsWith("-") && !isDashDashArgument();
		}
		
		public boolean isDashDashArgument() {
			return argumentName.startsWith("--");
		}
		
		/**
		 * @return true if the argument name is of length 1 (two if this is a dash argument)
		 */
		public boolean isShortArgument() {
			return ((isDashArgument() && (argumentName.length() == 2)) || (argumentName.length() == 1));
		}
		
		public boolean hasSubOptions() {
			return (subOptions != null);
		}

		public String getArgumentName() {
			return argumentName;
		}
		
		/**
		 * @return if {@link #isDashArgument()} returns true, this retuns the argument name without the prefacing dash,
		 * 				otherwise this returns the entire argument name
		 */
		public String getDashlessArgumentName() {
			if (isDashArgument()) {
				return argumentName.substring(1);
			}
			
			return argumentName;
		}

		public String getSampleValue() {
			return sampleValue;
		}

		public String getDescription() {
			return description;
		}
		
		public String getSubOptions() {
			return subOptions;
		}

		@Override
		public int hashCode() {
			return Objects.hash(argumentName);
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj) {
				return true;
			}
			
			if (obj == null) {
				return false;
			}
			
			if (getClass() != obj.getClass()) {
				return false;
			}
			
			final Argument other = (Argument) obj;
			return Objects.equals(argumentName, other.argumentName);
		}
	}
}
