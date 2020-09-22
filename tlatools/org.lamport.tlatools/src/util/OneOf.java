package util;

import java.util.Optional;
import java.util.function.Consumer;
import java.util.function.Function;

/**
 * Class enabling functional handling of multiple possible return types.
 *
 * Source: https://stackoverflow.com/a/26164155/2852699
 *
 * @param <T1> The type of the first possible value.
 * @param <T2> The type of the second possible value.
 * @param <T3> The type of the third possible value.
 */
public final class OneOf<T1,T2,T3>
{
	/**
	 * The first possible value.
	 */
    private final Optional<T1> first;
    
    /**
     * The second possible value.
     */
    private final Optional<T2> second;

    /**
     * The third possible value.
     */
    private final Optional<T3> third;

    /**
     * Constructs an instance for the first value.
     * @param value The first value.
     * @return A OneOf instance with the first value.
     */
	public static <T1,T2,T3> OneOf<T1,T2,T3> first(T1 value)
	{
        return new OneOf<>(Optional.of(value), Optional.empty(), Optional.empty());
    }

	public static <T1,T2,T3> OneOf<T1,T2,T3> second(T2 value)
	{
        return new OneOf<>(Optional.empty(), Optional.of(value), Optional.empty());
    }

	public static <T1,T2,T3> OneOf<T1,T2,T3> third(T3 value)
	{
        return new OneOf<>(Optional.empty(), Optional.empty(), Optional.of(value));
	}

    /**
     * Applies a map to all possible values.
     * @param firstFunc Function to apply to first value, if present.
     * @param secondFunc Function to apply to second value, if present.
     * @param thirdFunc Function to apply to third value, if present.
     * @return
     */
    public <NT> NT map(
        Function<? super T1, ? extends NT> firstFunc,
        Function<? super T2, ? extends NT> secondFunc,
        Function<? super T3, ? extends NT> thirdFunc)
    {
    	Optional<NT> firstResult = this.first.map(firstFunc);
    	Optional<NT> secondResult = this.second.map(secondFunc);
    	Optional<NT> thirdResult = this.third.map(thirdFunc);
    	return firstResult.orElseGet(() -> secondResult.orElseGet(() -> thirdResult.get()));
    }

    public <NT> OneOf<NT,T2,T3> mapFirst(Function<? super T1, ? extends NT> firstFunc)
    {
    	return new OneOf<>(this.first.map(firstFunc), this.second, this.third);
    }

    public <NT> OneOf<T1,NT,T3> mapSecond(Function<? super T2, ? extends NT> secondFunc)
    {
    	return new OneOf<>(this.first, this.second.map(secondFunc), this.third);
    }

    public <NT> OneOf<T1,T2,NT> mapThird(Function<? super T3, ? extends NT> thirdFunc)
    {
    	return new OneOf<>(this.first, this.second, this.third.map(thirdFunc));
    }

    public void ifPresent(
    		Consumer<? super T1> firstFunc,
    		Consumer<? super T2> secondFunc,
    		Consumer<? super T3> thirdFunc)
    {
        this.first.ifPresent(firstFunc);
        this.second.ifPresent(secondFunc);
        this.third.ifPresent(thirdFunc);
    }

    private OneOf(Optional<T1> first, Optional<T2> second, Optional<T3> third)
    {
    	this.first = first;
    	this.second = second;
    	this.third = third;
    }
}