package tlc2.util.statistics;

/**
 * Keeps statistics about any samples added.
 */
public interface IBucketStatistics {

	/**
	 * @param amount
	 *            Add a sample to the statistics. Allowed range is 0 <= sample <=
	 *            Integer.MAX_VALUE
	 */
	void addSample(int amount);

	/**
	 * @return The sum of all values in all buckets (might exceed int)
	 */
	long getObservations();

	/**
	 * @return The median
	 */
	int getMedian();

	/**
	 * @return The mean
	 */
	double getMean();

	/**
	 * @return The minimum
	 */
	int getMin();

	/**
	 * @return The maximum
	 */
	int getMax();

	/**
	 * @return The standard deviation
	 */
	double getStdDev();

	/**
	 * @param quantile 0 <= d <= 1.0 (adjusted to closet limit if smaller or larger)
	 * @return The given percentile
	 */
	double getPercentile(double quantile);

}