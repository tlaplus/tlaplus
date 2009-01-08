// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
package tla2sany.drivers;


class FrontEndException extends Exception {

  Exception ex;

  public FrontEndException(Exception e) { ex = e; }

}
