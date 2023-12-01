----------------------- MODULE _TLAPlusDebugger ------------------------

LOCAL _debuggerInvariant ==
	\* The nested definition is needed because TLC only supports re-defining
	\* a nested definition (on the fly), but not an invariant such as
	\* _TLAPlusDebuggerInvariant.
    TRUE
    
_TLAPlusDebuggerInvariant ==
	_debuggerInvariant

========================================================================