// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Last modified on Wed Jul 11 00:00:55 PDT 2001 by yuanyu
package util;

import java.io.EOFException;
import java.io.File;
import java.io.IOException;
import java.io.Serializable;
import java.util.HashMap;
import java.util.Map;

import tlc2.output.EC;
import tlc2.tool.distributed.InternRMI;

/**
 * Storage for the UniqueStrings.  It stores them in a hash table using
 * simple linear hashing.
 * @see {@link VarLocMap} for more information 
 * @author Yuan Yu, Simon Zambrovski
 */
public final class InternTable implements Serializable
{
}
