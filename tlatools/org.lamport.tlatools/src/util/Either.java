package util;

import java.util.Optional;
import java.util.function.Consumer;
import java.util.function.Function;

/**
 * Class enabling functional handling of multiple possible return types.
 *
 * Based on code from:
 * https://stackoverflow.com/a/26164155/2852699
 *
 * @param <L> The type of the left possible value.
 * @param <R> The type of the right possible value.
 */
public final class Either<L,R>
{
	/**
	 * The left possible value.
	 */
    private final Optional<L> left;

    /**
     * The right possible value.
     */
    private final Optional<R> right;

    /**
     * Constructs an instance for the left value.
     * @param value The left value.
     * @return An Either instance with the left value.
     */
	public static <L,R> Either<L,R> left(L value)
	{
        return new Either<>(Optional.of(value), Optional.empty());
    }

    /**
     * Constructs an instance for the right value.
     * @param value The right value.
     * @return An Either instance with the right value.
     */
    public static <L,R> Either<L,R> right(R value)
    {
        return new Either<>(Optional.empty(), Optional.of(value));
    }

    /**
     * Applies a map to both possible values.
     * @param lFunc Function to apply to left value, if present.
     * @param rFunc Function to apply to right value, if present.
     * @return
     */
    public <T> T map(
        Function<? super L, ? extends T> lFunc,
        Function<? super R, ? extends T> rFunc)
    {
        return this.left.<T>map(lFunc).orElseGet(() -> this.right.map(rFunc).get());
    }

    /**
     * Applies a function to the left value, if present.
     * @param <T> The function return type.
     * @param lFunc Function to apply to left value, if present.
     * @return An Either instance with the function applied.
     */
    public <T> Either<T,R> mapLeft(Function<? super L, ? extends T> lFunc)
    {
        return new Either<>(this.left.map(lFunc), right);
    }

    /**
     * Applies a function to the right value, if present.
     * @param <T> The function return type.
     * @param lFunc Function to apply to right value, if present.
     * @return An Either instance with the function applied.
     */
    public <T> Either<L,T> mapRight(Function<? super R, ? extends T> rFunc)
    {
        return new Either<>(this.left, this.right.map(rFunc));
    }

    /**
     * Consumes values if present.
     * @param lFunc Consumer for left value.
     * @param rFunc Consumer for right value.
     */
    public void ifPresent(Consumer<? super L> lFunc, Consumer<? super R> rFunc)
    {
        this.left.ifPresent(lFunc);
        this.right.ifPresent(rFunc);
    }

    /**
     * Private constructor accepting values for both values. Intended to be
     * called with Optional.empty() provided for all but one value.
     * @param left The left value.
     * @param right The right value.
     */
    private Either(Optional<L> left, Optional<R> right)
    {
      this.left = left;
      this.right = right;
    }
}