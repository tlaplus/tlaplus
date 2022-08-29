package tlc2.util;

import java.io.IOException;
import java.util.BitSet;

public class BitSetUtilities {

    public static String generateString(final BitSet bitSet, final int start, final int length, final char one, final char zero) {
        final StringBuilder buf = new StringBuilder(length);

        for (int i = 0; i < length; i++) {
            if (bitSet.get(start + i)) {
                buf.append(one);
            } else {
                buf.append(zero);
            }
        }
        return "[" + buf.reverse() + "]";
    }

    /**
     * Write the bit vector to a file.
     */
    public static void write(final BitSet bitSet, final BufferedRandomAccessFile raf) throws IOException {
        final var words = bitSet.toLongArray();

        raf.writeNat(words.length);

        for (final long word : words) {
            raf.writeLong(word);
        }
    }

    /**
     * Read a bit vector from a file
     */
    public static BitSet fromFile(final BufferedRandomAccessFile raf) throws IOException {
        final int wordCount = raf.readNat();

        final long[] words = new long[wordCount];

        for (int i = 0; i < wordCount; i++) {
            words[i] = raf.readLong();
        }

        return BitSet.valueOf(words);
    }
}
