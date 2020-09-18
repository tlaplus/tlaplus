package classloadhelper;

import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

/**
 * Utility methods to easy operations via reflection.
 * Derived from code written by Lê Anh Quân here (MIT licensed):
 * 	https://github.com/quanla/classreloading
 */
public class ReflectUtil {

	/**
	 * Constructs an instance of the given class, using a constructor without
	 * parameters.
	 * @param classHandle Handle to the class to construct.
	 * @return An instance of the constructed class.
	 */
    public static Object construct(Class<?> classHandle) {
    	try {
			Constructor<?> constructorHandle = classHandle.getConstructor();
			return constructorHandle.newInstance();
    	} catch (NoSuchMethodException | InstantiationException | IllegalAccessException | InvocationTargetException e) {
    		throw new RuntimeException(e);
    	}
    }
	
    /**
     * Constructs an instance of the given class, using a constructor with
     * parameters.
     * @param classHandle Handle to the class to construct.
     * @param paramTypes Expected types of parameters in the constructor.
     * @param params Parameters to give to constructor.
     * @return An instance of the constructed class.
     */
    public static Object constructWithParams(Class<?> classHandle, Class<?>[] paramTypes, Object[] params) {
    	try {
			Constructor<?> constructorHandle = classHandle.getConstructor(paramTypes);
			return constructorHandle.newInstance(params);
    	} catch (NoSuchMethodException | InstantiationException | IllegalAccessException | InvocationTargetException e) {
    		throw new RuntimeException(e);
    	}
    }
    
    /**
     * Invokes a method in the class. Does not currently support inheritance.
     * @param classHandle Handle to the class containing the method.
     * @param methodName Name of the method in the class.
     * @param classInstance Instance of class on which to invoke method.
     * @return Result of method invocation.
     */
    public static Object invokeMethod(
    		Class<?> classHandle,
    		String methodName,
    		Object classInstance) {
    	try {
    		Method methodHandle = classHandle.getMethod(methodName);
    		return methodHandle.invoke(classInstance);
    	} catch (NoSuchMethodException | IllegalAccessException | IllegalArgumentException | InvocationTargetException e) {
    		throw new RuntimeException(e);
    	}
    }
    
    /**
     * Invokes a method in the class, with parameters. Does not currently
     * support inheritance.
     * @param classHandle Handle to the class containing the method.
     * @param methodName Name of the method in the class.
     * @param classInstance Instance of class on which to invoke method.
     * @param paramClassHandles Expected parameter types.
     * @param params Parameter values.
     * @return Result of method invocation.
     */
    public static Object invokeMethodWithParams(
    		Class<?> classHandle,
    		String methodName,
    		Object classInstance,
    		Class<?>[] paramClassHandles,
    		Object[] params) {
    	try {
			Method methodHandle = classHandle.getMethod(methodName, paramClassHandles);
			return methodHandle.invoke(classInstance, params);
    	} catch (NoSuchMethodException | IllegalAccessException | IllegalArgumentException | InvocationTargetException e) {
    		throw new RuntimeException(e);
    	}
    }
    
    /**
     * Invokes a method in the class, with parameters, by name. Does not
     * currently support inheritance.
     * WARNING: if the class has multiple methods by the same name, Java will
     * select one NONDETERMINISTICALLY.
     * @param classHandle Handle to the class containing the method.
     * @param methodName Name of the method in the class.
     * @param classInstance Instance of class on which to invoke method.
     * @param params Parameter values.
     * @return Result of method invocation.
     */
    public static Object invokeMethodByName(
    		Class<?> classHandle,
    		String methodName,
    		Object classInstance,
    		Object... params) {
    	try {
    		for (Method methodHandle : classHandle.getMethods()) {
    			if (methodHandle.getName().equals(methodName)) {
					return methodHandle.invoke(classInstance, params);
    			}
    		}
    		
    		throw new NoSuchMethodException(methodName);
    	} catch (NoSuchMethodException | IllegalAccessException | IllegalArgumentException | InvocationTargetException e) {
    		throw new RuntimeException(e);
    	}
    }
    
    
    /**
     * Invokes a static method in the class. Does not currently support
     * inheritance.
     * @param classHandle Handle to the class containing the method.
     * @param methodName Name of the method in the class.
     * @return Result of method invocation.
     */
    public static Object invokeStaticMethod(
    		Class<?> classHandle,
    		String methodName) {
    	return ReflectUtil.invokeMethod(classHandle, methodName, null);
    }

    /**
     * Invokes a static method in the class, with parameters. Does not currently
     * support inheritance.
     * @param classHandle Handle to the class containing the method.
     * @param methodName Name of the method in the class.
     * @param paramClassHandles Expected parameter types.
     * @param params Parameter values.
     * @return Result of method invocation.
     */
    public static Object invokeStaticMethodWithParams(
    		Class<?> classHandle,
    		String methodName,
    		Class<?>[] paramClassHandles,
    		Object[] params) {
    	return ReflectUtil.invokeMethodWithParams(classHandle, methodName, null, paramClassHandles, params);
    }
    
	
    /**
     * Sets value of static field in a class.
     * @param classHandle Handle to class containing the field.
     * @param fieldName Name of the field in the class.
     * @param fieldValue Value to which to set field.
     */
    public static void setStaticFieldValue(Class<?> classHandle, String fieldName, Object fieldValue) {
    	try {
			Field fieldHandle = classHandle.getDeclaredField(fieldName);
			fieldHandle.set(null, fieldValue);
		} catch (NoSuchFieldException | SecurityException | IllegalArgumentException | IllegalAccessException e) {
			throw new RuntimeException(e);
		}
    }
}
