---
title: TLA+ Animation Guide
description: Learn to create visual SVG animations from TLA+ specifications using animation files (_anim.tla) and MCP server tools for debugging and documentation.
---

# TLA+ Animation Guide

This guide explains how to create TLA+ animation files (`_anim.tla`) that generate SVG visualizations of your specifications. Using the TLA+ MCP server tools, you can validate your animations and generate visual representations of system behavior for debugging and documentation.

## Table of Contents

1. [Overview](#overview)
2. [Quick Start](#quick-start)
3. [Animation File Structure](#animation-file-structure)
4. [Creating Your First Animation](#creating-your-first-animation)
5. [Complete Example](#complete-example)
6. [SVG Element Reference](#svg-element-reference)
7. [Advanced Animation Techniques](#advanced-animation-techniques)
8. [Using MCP Server Tools](#using-mcp-server-tools)
9. [Best Practices](#best-practices)
10. [Troubleshooting](#troubleshooting)
11. [Gallery of Animation Patterns](#gallery-of-animation-patterns)
12. [Appendix: Real-World Animation Examples](#appendix-real-world-animation-examples)

## Overview

TLA+ animations transform behaviors of abstract specifications into visual SVG representations that show how your system evolves through different states. Animation files (`_anim.tla`) extend your original specifications with visualization logic.

### Key Benefits

- **Visual Debugging**: See how state variables change through system execution
- **Documentation**: Generate diagrams that illustrate system behavior
- **Communication**: Share visual representations with stakeholders
- **Automated Generation**: Create SVG files for each state in a trace
- **Validation**: Use MCP tools to verify animation correctness

## Quick Start

### 1. Create Animation File

For a specification `MySpec.tla`, create `MySpec_anim.tla`:

```tla
---- MODULE MySpec_anim ----
EXTENDS TLC, SVG, IOUtils, MySpec

\* Define visual representation
AnimView == Circle(50, 50, 20, ("fill" :> "blue"))

\* Wrap view in SVG document (single source of truth for viewBox)
AnimDoc == SVGDoc(AnimView, 0, 0, 100, 100, <<>>)

\* Enable SVG file generation (for TLC model checking)
AnimAlias ==
    [state |-> state] @@  \* Include state variables for debugging
    [_anim |-> SVGSerialize(AnimDoc, "MySpec_anim_", TLCGet("level"))]

\* Alternative: For interactive debugging in TLA+ Debugger
AnimWatch ==
    SVGSerialize(AnimDoc, "MySpec_anim", 0)
====
```

### 2. Validate Animation

Use the MCP server to check syntax:
```
tlaplus_mcp_sany_parse MySpec_anim.tla
```

### 3. Generate Animation SVGs

Create configuration file and use MCP to explore states:
```
tlaplus_mcp_tlc_explore MySpec_anim.tla -depth 10
```

## Animation File Structure

### Essential Components

Every animation file follows this structure:

```tla
---- MODULE MySpec_anim ----
EXTENDS TLC,        \* TLC built-ins (@@, :>, etc.)
        SVG,        \* SVG element constructors
        IOUtils,    \* File serialization
        MySpec      \* Your original specification

\* Visual representation logic
AnimView == \* Returns SVG elements based on current state

\* File generation configuration (choose one approach)
AnimAlias == \* For TLC model checking (generates numbered frames)
AnimWatch == \* For TLA+ Debugger (live preview)
====
```

### Key Components Explained

1. **AnimView**: The main operator that creates SVG elements based on the current state. This is the core of your animation - it defines how state variables map to visual properties.
2. **AnimDoc**: Wraps `AnimView` in an SVG document with viewBox parameters. This provides a single source of truth for document dimensions, eliminating duplication between `AnimAlias` and `AnimWatch`.
3. **AnimAlias** or **AnimWatch**: Two different approaches for serializing SVG to disk (detailed below)
4. **SVG Module**: Provides constructors for visual elements (Circle, Rect, Text, etc.)
5. **IOUtils Module**: Handles file writing operations
6. **State Mapping**: Your logic that transforms state variables into visual properties

## Serialization Approaches: AnimAlias vs AnimWatch

While `AnimView` defines *what* to visualize, you need a serialization mechanism to *output* the SVG frames. TLA+ animations support two approaches, each suited to different workflows:

### AnimAlias: For Screencasts and Animation Sequences

**Use Case**: Creating animation sequences for documentation, presentations, or screencasts.

**How it works**:
- Add `ALIAS AnimAlias` to your TLC configuration file (`.cfg`)
- TLC automatically evaluates `AnimAlias` at each state during counterexample generation
- Each state generates a **unique numbered SVG file**
- Frame numbering uses `TLCGet("level")` to create sequential files

**Example**:
```tla
AnimDoc == SVGDoc(AnimView, 0, 0, 760, 420, <<>>)

AnimAlias ==
    [active |-> active, color |-> color, counter |-> counter] @@
    [_anim |-> SVGSerialize(
        AnimDoc,                  \* Reusable document
        "MySpec_anim_",           \* Filename prefix
        TLCGet("level"))]         \* Unique frame number
```

**Generated files**: `MySpec_anim_0.svg`, `MySpec_anim_1.svg`, `MySpec_anim_2.svg`, ...

**Configuration file**:
```
INIT Init
NEXT Next
ALIAS AnimAlias
```

### AnimWatch: For Interactive Debugging

**Use Case**: Live visualization during step-by-step debugging sessions.

**How it works**:
- Use as a Watch expression in the TLA+ Debugger
- Each evaluation **overwrites the same SVG file** (frame number 0)
- Pair with a live SVG viewer that auto-refreshes (e.g., [SVG extension](https://open-vsx.org/extension/jock/svg))
- See animation update in real-time as you step through execution

**Example**:
```tla
AnimDoc == SVGDoc(AnimView, 0, 0, 760, 420, <<>>)

AnimWatch ==
    SVGSerialize(
        AnimDoc,                  \* Reusable document
        "MySpec_anim",     \* Filename prefix
        0)                        \* Frame 0 (overwrites each time)
```

**Generated file**: `MySpec_anim00.svg` (single file, continuously updated)

**Debugger usage**:
When debugging `MySpec.tla`, add this watch expression:
```
LET A == INSTANCE MySpec_anim IN A!AnimWatch
```

### Choosing Between AnimAlias and AnimWatch

You don't need to choose—include *both* in your animation file! Use `AnimAlias` for documentation and `AnimWatch` for development/debugging.

## Creating Your First Animation

### Step 1: Plan Your Visualization

Consider what to visualize and how:
- **State Variables**: Map each to visual properties (color, position, shape)
- **Visual Language**: Choose consistent meanings (red=error, green=active)
- **Layout**: Decide spatial arrangement (grid, circle, hierarchy)

### Step 2: Implement AnimView

Start with basic visual mapping:

```tla
---- MODULE DistributedSystem_anim ----
EXTENDS TLC, SVG, IOUtils, SequencesExt, DistributedSystem

\* Layout constants
NodeSpacing == 80
BaseX == 50
BaseY == 50

\* Convert sets to deterministic sequences
NodeSeq == SetToSeq(Nodes)
NodeIndex == [n \in Nodes |-> 
    CHOOSE i \in 1..Len(NodeSeq) : NodeSeq[i] = n]

\* Create visual elements
NodeElement(n) ==
    LET x == BaseX + (NodeIndex[n] - 1) * NodeSpacing
        y == BaseY
        color == CASE state[n] = "leader" -> "gold"
                   [] state[n] = "follower" -> "lightblue"
                   [] OTHER -> "gray"
    IN Group(<<
        Circle(x, y, 25, ("fill" :> color @@ "stroke" :> "black")),
        Text(x, y + 5, ToString(n), 
            ("text-anchor" :> "middle" @@ "font-size" :> "14px"))
    >>, <<>>)

\* Combine into animation view
AnimView == Group([n \in 1..Len(NodeSeq) |-> NodeElement(NodeSeq[n])], 
                  ("transform" :> "scale(1.2)"))
```

### Step 3: Add Serialization Operators

Enable file generation:

```tla
\* Wrap view in SVG document
AnimDoc == SVGDoc(AnimView, 0, 0, 400, 200, <<>>)

\* For TLC model checking (generates numbered frames)
AnimAlias ==
    [_anim |-> SVGSerialize(AnimDoc, "DistributedSystem_anim_", TLCGet("level"))]

\* For interactive debugging (live preview)
AnimWatch ==
    SVGSerialize(AnimDoc, "DistributedSystem_anim", 0)
```

## Complete Example

Let's build a complete animation for a simple counter system with multiple nodes:

### 1. Original Specification

```tla
---- MODULE CounterSystem ----
EXTENDS Naturals
CONSTANT Nodes
VARIABLE counter

Init == counter = [n \in Nodes |-> 0]

Increment(n) == counter' = [counter EXCEPT ![n] = @ + 1]

Next == \E n \in Nodes : Increment(n)
====
```

### 2. Animation Specification

```tla
---- MODULE CounterSystem_anim ----
EXTENDS TLC, SVG, IOUtils, SequencesExt, CounterSystem

\* Layout configuration
NodeRadius == 30
NodeSpacing == 120
BaseY == 100

\* Deterministic node ordering
NodeSeq == SetToSeq(Nodes)
NodeIndex == [n \in Nodes |-> CHOOSE i \in 1..Len(NodeSeq) : NodeSeq[i] = n]

\* Calculate positions
NodeX(n) == 50 + (NodeIndex[n] - 1) * NodeSpacing

\* Color based on counter value
NodeColor(n) == 
    LET c == counter[n]
    IN CASE c = 0 -> "#e0e0e0"
         [] c < 5 -> "#81c784" 
         [] c < 10 -> "#ffd54f"
         [] OTHER -> "#e57373"

\* Create node visualization
NodeVis(n) ==
    LET x == NodeX(n)
    IN Group(<<
        \* Node circle
        Circle(x, BaseY, NodeRadius, 
            ("fill" :> NodeColor(n) @@ "stroke" :> "#333" @@ "stroke-width" :> "2")),
        \* Node name
        Text(x, BaseY - 40, ToString(n), 
            ("text-anchor" :> "middle" @@ "font-size" :> "14px" @@ "font-weight" :> "bold")),
        \* Counter value
        Text(x, BaseY + 5, ToString(counter[n]), 
            ("text-anchor" :> "middle" @@ "font-size" :> "20px" @@ "font-weight" :> "bold")),
        \* Value label
        Text(x, BaseY + 50, "count: " \o ToString(counter[n]), 
            ("text-anchor" :> "middle" @@ "font-size" :> "12px" @@ "fill" :> "#666"))
    >>, <<>>)

\* Legend
Legend == Group(<<
    Text(50, 30, "Counter System Animation", 
        ("font-size" :> "18px" @@ "font-weight" :> "bold")),
    Text(50, 50, "Gray: 0, Green: 1-4, Yellow: 5-9, Red: 10+", 
        ("font-size" :> "12px" @@ "fill" :> "#666"))
>>, <<>>)

\* Step number display
StepNumber == 
    Text(90 + Cardinality(Nodes) * NodeSpacing, 190, 
         "Step " \o ToString(TLCGet("level")), 
         ("text-anchor" :> "end" @@ 
          "font-size" :> "12px" @@ 
          "font-family" :> "monospace" @@ 
          "fill" :> "#666"))

\* Main animation view
AnimView == 
    Group(<<Legend, StepNumber>> \o [i \in 1..Len(NodeSeq) |-> NodeVis(NodeSeq[i])], <<>>)

\* Wrap view in document structure
AnimDoc == SVGDoc(AnimView, 0, 0, 100 + Cardinality(Nodes) * NodeSpacing, 200, <<>>)

\* TLC animation export (for screencasts)
AnimAlias ==
    [counter |-> counter] @@
    [_anim |-> SVGSerialize(AnimDoc, "CounterSystem_anim_", TLCGet("level"))]

\* Interactive debugging (for live preview)
AnimWatch ==
    SVGSerialize(AnimDoc, "CounterSystem_anim", 0)
====
```

### 3. Configuration File (for AnimAlias)

```
CONSTANT Nodes = {n1, n2, n3}
INIT Init
NEXT Next
ALIAS AnimAlias
```

### 4. Running the Animation

Use MCP to generate animation frames:

```
# First validate the syntax
tlaplus_mcp_sany_parse CounterSystem_anim.tla

# Then generate animation states
tlaplus_mcp_tlc_explore CounterSystem_anim.tla -depth 20
```

This will create SVG files: `CounterSystem_anim_0.svg`, `CounterSystem_anim_1.svg`, etc.

This example demonstrates:
- Deterministic node ordering with `SetToSeq`
- Dynamic color mapping based on state
- Clear visual hierarchy with title, nodes, and labels
- Proper viewBox calculation for any number of nodes
- Complete AnimView and AnimAlias implementation

## SVG Element Reference

### Basic Shapes

#### Circle
```tla
Circle(cx, cy, r, attrs)
\* Example: Circle(100, 100, 25, ("fill" :> "red" @@ "stroke" :> "black"))
```

#### Rectangle
```tla
Rect(x, y, width, height, attrs)
\* Example: Rect(50, 50, 100, 60, ("fill" :> "lightblue" @@ "rx" :> "5"))
```

#### Line
```tla
Line(x1, y1, x2, y2, attrs)
\* Example: Line(0, 0, 100, 100, ("stroke" :> "black" @@ "stroke-width" :> "2"))
```

#### Text
```tla
Text(x, y, content, attrs)
\* Example: Text(50, 50, "Node 1", ("text-anchor" :> "middle" @@ "font-size" :> "14px"))
```

#### Image
```tla
Image(x, y, width, height, href, attrs)
\* Example: Image(10, 10, 20, 20, "https://www.svgrepo.com/show/438355/car.svg", <<>>)
```

### Container Elements

#### Group
```tla
Group(children, attrs)
\* Example: Group(<<circle1, text1>>, ("transform" :> "translate(50, 50)"))
```

#### Svg
```tla
Svg(children, attrs)
\* SVG container element
\* Example: Svg(<<circle1, rect1>>, ("width" :> "400" @@ "height" :> "300"))
```

#### SVGDoc
```tla
SVGDoc(children, vbX, vbY, vbW, vbH, attrs)
\* Creates a complete SVG document with viewBox and standard attributes
\* Parameters:
\*   children: A sequence of SVG elements
\*   vbX, vbY: Top-left corner coordinates of the viewBox
\*   vbW, vbH: Width and height of the viewBox
\*   attrs: Additional attributes to merge
\* 
\* Example: SVGDoc(myElements, 0, 0, 800, 600, ("id" :> "main-svg"))
\* Automatically includes xmlns and xmlns:xlink attributes
```

### Low-Level Constructor

#### SVGElem
```tla
SVGElem(name, attrs, children, innerText)
\* Generic SVG element constructor for any element type
\* Parameters:
\*   - name: String name of the SVG element (e.g., "circle", "rect", "path")
\*   - attrs: Record of attributes
\*   - children: Sequence of child elements (use <<>> for none)
\*   - innerText: Text content (use "" for none)

\* Example: Custom path element
SVGElem("path", 
    ("d" :> "M 10 10 L 90 90 L 10 90 Z" @@ 
     "fill" :> "orange" @@ 
     "stroke" :> "black"), 
    <<>>, 
    "")

\* Example: Custom polygon
SVGElem("polygon",
    ("points" :> "50,10 90,40 90,90 50,120 10,90 10,40" @@
     "fill" :> "lime" @@
     "stroke" :> "purple" @@
     "stroke-width" :> "1"),
    <<>>,
    "")
```

### File Generation Utilities

#### SVGSerialize

```tla
SVGSerialize(svg, frameNamePrefix, frameNumber)
\* Serializes an SVG element to a file on disk
\* Parameters:
\*   svg: The SVG element/document to serialize
\*   frameNamePrefix: String prefix for the output filename
\*   frameNumber: Numeric identifier for unique filenames
\* Creates: "<frameNamePrefix><frameNumber>.svg"
\*
\* Example: Save animation frame
\* SVGSerialize(
\*     SVGDoc(myElements, 0, 0, 800, 600, <<>>),
\*     "animation_frame_", 
\*     TLCGet("level"))
\* \* Creates: animation_frame_1.svg, animation_frame_2.svg, etc.
```

### Attribute Syntax

Use the `@@` operator to combine attributes:

```tla
("fill" :> "blue" @@ 
 "stroke" :> "black" @@ 
 "stroke-width" :> "2" @@
 "opacity" :> "0.8")
```

## Using MCP Server Tools

### Validating Animation Files

Before generating animations, validate your syntax:

```
tlaplus_mcp_sany_parse MySpec_anim.tla
```

This checks for:
- Correct TLA+ syntax
- Proper module extensions
- Valid operator definitions

### Generating Animation SVGs

To explore states and generate SVG files:

```
tlaplus_mcp_tlc_explore MySpec_anim.tla -depth 10
```

This will:
1. Explore the state space up to depth 10
2. Generate SVG files for each state
3. Name files as `MySpec_anim_0.svg`, `MySpec_anim_1.svg`, etc.

### Configuration Files

Create a `.cfg` file to control animation generation:

```
INIT Init
NEXT Next
ALIAS AnimAlias
```

### Post-Processing SVG Files

After generation, you can:
- View individual SVG files in any browser
- Create animated sequences using ImageMagick:
  ```bash
  convert -delay 100 -loop 0 *.svg animation.gif
  ```
- Generate video presentations with ffmpeg

## Advanced Animation Techniques

### Dynamic Layouts

Handle variable numbers of elements with adaptive layouts:

```tla
\* Grid layout that adjusts to element count
GridLayout(elements, columns) ==
    LET count == Len(elements)
        rows == (count + columns - 1) \div columns
        cellWidth == 100
        cellHeight == 80
    IN [i \in 1..count |->
        LET row == (i - 1) \div columns
            col == (i - 1) % columns
        IN [x |-> col * cellWidth + 50,
            y |-> row * cellHeight + 50]]

\* Circular layout for connected systems
CircularLayout(nodeCount, radius) ==
    LET angle(i) == 2 * 314 * i \div (nodeCount * 100)  \* Approximation of 2π
    IN [i \in 1..nodeCount |->
        [x |-> 200 + radius * Cos(angle(i)),
         y |-> 200 + radius * Sin(angle(i))]]
```

### Interactive Visual Elements

Create responsive visualizations:

```tla
\* Highlight on state change
HighlightedElement(x, y, elem, changed) ==
    IF changed THEN
        Group(<<
            \* Highlight ring
            Circle(x, y, 30, ("fill" :> "none" @@ 
                             "stroke" :> "orange" @@ 
                             "stroke-width" :> "3")),
            elem
        >>, <<>>)
    ELSE elem

\* Status indicators with icons
StatusIcon(x, y, status) ==
    CASE status = "running" -> 
            Image(x-10, y-10, 20, 20, "https://www.svgrepo.com/show/532245/gear-alt.svg", <<>>)
      [] status = "error" -> 
            Image(x-10, y-10, 20, 20, "https://www.svgrepo.com/show/497000/danger.svg", <<>>)
      [] status = "success" -> 
            Image(x-10, y-10, 20, 20, "https://www.svgrepo.com/show/404945/check-mark.svg", <<>>)
      [] OTHER -> 
            Circle(x, y, 5, ("fill" :> "gray"))
```

### Complex System Visualizations

Combine techniques for sophisticated animations:

```tla
\* Message passing with visual trail
MessagePath(from, to, messages) ==
    LET path == Line(from.x, from.y, to.x, to.y, 
                    ("stroke" :> "lightgray" @@ 
                     "stroke-dasharray" :> "5,5"))
        msgDots == [m \in 1..Len(messages) |->
            LET progress == messages[m].progress
                x == from.x + (to.x - from.x) * progress \div 100
                y == from.y + (to.y - from.y) * progress \div 100
            IN Circle(x, y, 4, ("fill" :> messages[m].type))]
    IN Group(<<path>> \o msgDots, <<>>)

\* Hierarchical tree visualization
TreeNode(node, level, position) ==
    LET x == position * 60
        y == level * 80 + 50
        children == GetChildren(node)
    IN Group(<<
        \* Node representation
        Rect(x-25, y-15, 50, 30, 
            ("fill" :> NodeColor(node) @@ "rx" :> "5")),
        Text(x, y, node.label, 
            ("text-anchor" :> "middle" @@ "font-size" :> "12px")),
        \* Connections to children
        [c \in 1..Len(children) |->
            Line(x, y+15, 
                 position * 60 + (c - (Len(children)+1)/2) * 40, 
                 (level+1) * 80 + 35,
                 ("stroke" :> "gray"))]
    >>, <<>>)
```

## Best Practices

### 1. Always Use Deterministic Ordering

Convert sets to sequences for consistent visualization:

```tla
\* Good: Deterministic sequence
NodeSeq == SetToSeq(Nodes)
NodeElements == [i \in 1..Len(NodeSeq) |-> DrawNode(NodeSeq[i])]

\* Bad: Non-deterministic set comprehension
\* NodeElements == {DrawNode(n) : n \in Nodes}  -- Don't do this!
```

### 2. Define Consistent Visual Language

Create reusable color schemes and constants:

```tla
\* Define once, use everywhere
ColorScheme == [
    active |-> "#28a745",    \* Green
    inactive |-> "#6c757d",  \* Gray  
    error |-> "#dc3545",     \* Red
    warning |-> "#ffc107"    \* Yellow
]

\* Standard sizes
NodeRadius == 20
IconSize == 16
Spacing == 60
```

### 3. Build Modular Components

Create reusable visual elements:

```tla
\* Reusable status badge
StatusBadge(x, y, status, count) ==
    Group(<<
        Circle(x, y, 8, ("fill" :> ColorScheme[status])),
        Text(x, y + 3, ToString(count), 
            ("text-anchor" :> "middle" @@ 
             "font-size" :> "10px" @@ 
             "fill" :> "white"))
    >>, <<>>)

\* Then use it consistently
NodeWithStatus(n) == 
    Group(<<
        NodeElement(n),
        StatusBadge(NodePos(n).x + 15, NodePos(n).y - 15, 
                   state[n], messageCount[n])
    >>, <<>>)
```

### 4. Handle Text Readability

Ensure labels are always legible:

```tla
\* Add backgrounds to text over complex visuals
LabelWithBackground(x, y, text) ==
    Group(<<
        Rect(x - Len(text) * 3, y - 8, Len(text) * 6, 16, 
            ("fill" :> "white" @@ 
             "opacity" :> "0.9" @@ 
             "rx" :> "2")),
        Text(x, y + 3, text, 
            ("text-anchor" :> "middle" @@ 
             "font-size" :> "11px"))
    >>, <<>>)
```

### 5. Maintain Consistent ViewBox for Animations

When creating TLA+ animations composed of multiple SVG frames, **it is essential to maintain a consistent `viewBox` across all frames** to ensure smooth and accurate playback. Each frame produced by `SVGSerialize` must share the same coordinate system to avoid visual misalignment. Avoid applying transformations that modify the effective `viewBox` between frames, and include sufficient padding when computing global bounds to account for dynamic content.

If the `viewBox` cannot be determined in advance, perform an initial pass to measure the maximum extents across all frames, then use those dimensions consistently for the final rendering.

### 6. Always Display Step Numbers

**Every animation frame must include a step number** to help track progression through the state space. The step number should appear in a consistent location across all frames, similar to how page numbers appear in documents.

```tla
\* Add step number in bottom-right corner
StepNumber == 
    Text(viewBoxWidth - 30, viewBoxHeight - 10, 
         "Step " \o ToString(TLCGet("level")), 
         ("text-anchor" :> "end" @@ 
          "font-size" :> "12px" @@ 
          "font-family" :> "monospace" @@ 
          "fill" :> "#666"))

\* Include in your AnimView
AnimView == 
    Group(<<YourMainVisualization, StepNumber>>, <<>>)
```

**Best practices for step numbers:**
- Position consistently (typically bottom-right or top-right corner)
- Use monospace font for alignment
- Choose subtle color that doesn't interfere with main content
- Include "Step" prefix for clarity
- Ensure adequate padding from frame edges

## Troubleshooting

### Common Issues and Solutions

#### No SVG Files Generated

**Symptom**: MCP exploration completes but no SVG files appear

**Solutions**:
1. Ensure `ALIAS AnimAlias` is in your `.cfg` file
2. Verify AnimAlias includes the `SVGSerialize` call
3. Check file permissions in output directory

#### Syntax Validation Fails

**Symptom**: `tlaplus_mcp_sany_parse` reports errors

**Solutions**:
1. Check all required modules are extended
2. Verify operator syntax, especially attribute records
3. Ensure proper use of `@@` and `:>` operators
4. Look for missing parentheses or brackets

#### Elements Not Showing State Changes

**Symptom**: SVG files look identical across states

**Solutions**:
1. Verify state variables are referenced in visual elements:
   ```tla
   \* Good: References state
   Circle(50, 50, 20, ("fill" :> IF active[node] THEN "green" ELSE "red"))
   
   \* Bad: Static color
   Circle(50, 50, 20, ("fill" :> "blue"))
   ```

2. Check that AnimView actually uses state variables

### Debugging Techniques

#### 1. Start Simple

Begin with minimal visualization to verify setup:

```tla
AnimView == Text(50, 50, "State: " \o ToString(state), 
                ("font-size" :> "20px"))
```

#### 2. Validate Generated SVG

Open generated SVG files directly in a browser to check for:
- Proper rendering
- Expected visual elements
- Correct attribute values

Because most LLMs and AI assistants cannot directly view or interpret SVG or PNG files, the best way for them to analyze TLA+ animations is by reading the SVG files as text and inspecting the SVG markup.
When an AI generates an animation at a user’s request, it should explain this limitation and ask the user to review the animation files to confirm that the visuals appear correct.

#### 3. Add Debug Information

Include state values in your visualization:

```tla
DebugInfo == Text(10, 10, "Step: " \o ToString(TLCGet("level")), 
                 ("font-size" :> "10px" @@ "fill" :> "gray"))
```

#### 4. Direct TLC Usage

For debugging or when MCP server is unavailable, you can use TLC directly:

```bash
# Run TLC on all animation configs and convert SVGs to PNGs
for f in $(ls *_anim.cfg); do 
    tlc -note -simulate -invlevel 10 ${f%.*}
done && for f in *.svg; do 
    rsvg-convert -o ${f%.*}.png $f
done
```

This approach:
- Runs TLC directly on each `*_anim.cfg` file
- Simulates 10 levels of state exploration
- Converts generated SVGs to PNG format for easier viewing
- Useful for batch processing and debugging animation issues

**Note**: Ensure you have `rsvg-convert` installed (part of librsvg package) for PNG conversion.

## Gallery of Animation Patterns

### Producer-Consumer Pattern

Visualize thread synchronization and buffer states:

```tla
\* Key elements:
\* - Circular nodes for thread states (green=running, red=waiting)
\* - Rectangular cells for buffer slots
\* - Text labels showing queue contents
\* - Status indicators for full/empty conditions
```

### Distributed System Pattern

Show node states and message passing:

```tla
\* Key elements:
\* - Nodes with role-based shapes/colors
\* - Message indicators between nodes
\* - State labels and counters
\* - Leader indicators (crown icons)
```

### Resource Allocation Pattern

Display resource ownership and conflicts:

```tla
\* Key elements:
\* - Resource holders highlighted
\* - Waiting queues visualized
\* - Conflict indicators
\* - State transitions animated
```

### State Machine Pattern

Illustrate state transitions clearly:

```tla
\* Key elements:
\* - Current state highlighted
\* - Previous states grayed out
\* - Transition arrows
\* - State invariant indicators
```

### Puzzle/Game Pattern

Create engaging visualizations:

```tla
\* Key elements:
\* - Icons for game pieces
\* - Board/environment layout
\* - Valid/invalid state indicators
\* - Success/failure highlighting
```

## Conclusion

TLA+ animation files provide powerful visualization capabilities for understanding and debugging specifications. By following this guide and using the MCP server tools, you can create effective animations that reveal system behavior through visual representation.

Key takeaways:
- Start with simple visualizations and iterate
- Use deterministic ordering for consistent results
- Leverage the SVG module's full capabilities
- Validate frequently with MCP tools
- Let the visualization serve your understanding

## Additional Resources

- [SVG Specification](https://www.w3.org/TR/SVG2/)
- [Spectacle](https://github.com/will62794/spectacle) - Spectacle is an interactive, web-based tool for exploring, visualizing, and sharing formal specifications written in the TLA+
- [TLA+ Examples Repository](https://github.com/tlaplus/Examples) - See `*_anim.tla` files
- [TLC Model Checker Documentation](https://lamport.azurewebsites.net/tla/tlc.html)

## Appendix: Real-World Animation Examples

The following examples demonstrate complete animation implementations for various TLA+ specifications. Each animation file extends its corresponding original specification, which can be found in the [Spectacle repository](https://github.com/will62794/spectacle/tree/master/specs).

### 1. Battery Relay System (`BatteryRelay_anim.tla`)

Visualizes electric vehicle charging station with battery swapping. This animation shows vehicles moving between left and right sides, battery level changes, and charging status.

**Original specification**: [`BatteryRelay.tla`](https://github.com/will62794/spectacle/tree/master/specs/BatteryRelay.tla)  
**Example animation**: [`BatteryRelay_anim.svg`](https://github.com/will62794/spectacle/tree/master/specs/BatteryRelay_anim.svg)

```tla
---- MODULE BatteryRelay_anim ----
EXTENDS TLC, SVG, SequencesExt, BatteryRelay

iconSize == 25

VehicleIcon(v) == 
    IF v = "Truck" THEN "assets/loaded-truck-svgrepo-com.svg"
    ELSE IF v = "Car" THEN "assets/fast-car-svgrepo-com.svg"
    ELSE IF v = "Bike" THEN "assets/motorbike-svgrepo-com.svg"
    ELSE IF v = "Scooter" THEN "assets/scooter-svgrepo-com.svg"
    ELSE "assets/car-svgrepo-com.svg"

Left ==
    LET order == SetToSeq(left)
        image(actor, o) == Image(10, o*35, iconSize, iconSize, 
                                VehicleIcon(actor), <<>>) 
    IN Group(SetToSeq({image(p, (CHOOSE i \in DOMAIN order : 
                       order[i] = p)) : p \in left}), [i \in {} |-> {}])

Right ==
    LET order == SetToSeq(right)
        image(actor, o) == Image(130, o*35, iconSize, iconSize, 
                                VehicleIcon(actor), <<>>) 
    IN Group(SetToSeq({image(p, (CHOOSE i \in DOMAIN order : 
                       order[i] = p)) : p \in right}), [i \in {} |-> {}])

BatteryIcon ==
    IF batteryLevel > 12 THEN "assets/battery-full-svgrepo-com.svg"
    ELSE IF batteryLevel > 7 THEN "assets/battery-mid-svgrepo-com.svg"
    ELSE IF batteryLevel > 0 THEN "assets/battery-low-svgrepo-com.svg"
    ELSE "assets/battery-empty-svgrepo-com.svg"

Battery ==
   IF batteryLeft
   THEN Group(<<Image(10, 5, iconSize, iconSize, BatteryIcon, <<>>), 
                Text(35, 23, ToString(batteryLevel), <<>>)>>, [i \in {} |-> {}])
   ELSE Group(<<Image(130, 5, iconSize, iconSize, BatteryIcon, <<>>), 
                Text(155, 23, ToString(batteryLevel), <<>>)>>, [i \in {} |-> {}])

Chargers ==
   Group(SetToSeq({
       Image(160, i, 30, 30, 
             IF right = Vehicles 
             THEN "assets/ev-plug-charging-svgrepo-com.svg"
             ELSE "assets/ev-plug-error-svgrepo-com.svg", <<>>)
       : i \in {40 + (i*35) : i \in 0..Cardinality(Vehicles)-1}
   }), [i \in {} |-> {}])

Empty ==
   Image(13, 20, 140, 140, "assets/battery-empty-symbolic-svgrepo-com.svg",
         IF batteryLevel < 0 THEN <<>> ELSE [hidden |-> "true"])

\* Step number in bottom-right corner
StepNumber == 
    Text(220, 190, "Step " \o ToString(TLCGet("level")), 
         ("text-anchor" :> "end" @@ "font-size" :> "12px" @@ 
          "font-family" :> "monospace" @@ "fill" :> "#666"))

AnimView == Group(<<Left, Right, Battery, Chargers, Empty, StepNumber>>, [i \in {} |-> {}])

AnimDoc == SVGDoc(AnimView, 0, 0, 230, 200, <<>>)

AnimAlias ==
    [left |-> left, right |-> right, 
     batteryLeft |-> batteryLeft, batteryLevel |-> batteryLevel] @@ 
    [_anim |-> SVGSerialize(AnimDoc, "BatteryRelay_anim_", TLCGet("level"))]

AnimWatch ==
    SVGSerialize(AnimDoc, "BatteryRelay_anim", 0)
====
```

**Key Techniques:**
- Dynamic icon selection based on vehicle type
- Battery level visualization with progressive icons and numeric display
- Spatial organization with left/right sides
- Charging status indicators that change based on state
- Empty battery warning overlay
- SetToSeq for deterministic ordering of vehicles

### 2. Blocking Queue (`BlockingQueue_anim.tla`)

Producer-consumer pattern with thread synchronization. Complete visualization showing producers, consumers, buffer state, and blocking conditions.

**Original specification**: [`BlockingQueue.tla`](https://github.com/will62794/spectacle/tree/master/specs/BlockingQueue.tla)  
**Example animation**: [`BlockingQueue_anim.svg`](https://github.com/will62794/spectacle/tree/master/specs/BlockingQueue_anim.svg)

```tla
---- MODULE BlockingQueue_anim ----
EXTENDS TLC, SVG, SequencesExt, BlockingQueue

\* Helper to get buffer element at index
ElemAt(i) == 
    IF i > Len(buffer) THEN "" ELSE buffer[i]

\* Layout constants
BUFFER_WIDTH == 45
BUFFER_HEIGHT == 35
CELL_SPACING == 8
THREAD_RADIUS == 20
THREAD_SPACING == 70
BASE_X == 60
BASE_Y == 80

BufferCellColor(i) == 
    IF ElemAt(i) = "" THEN "#f8f9fa" ELSE "#17a2b8"

BufferCell(i) == 
    LET x_pos == BASE_X + 150
        y_pos == BASE_Y + (i - 1) * (BUFFER_HEIGHT + CELL_SPACING)
        cell_content == IF ElemAt(i) = "" THEN "" ELSE ToString(ElemAt(i))
        text_color == IF ElemAt(i) = "" THEN "#6c757d" ELSE "white"
        value == Text(x_pos + 22, y_pos + 22, cell_content, 
                     ("text-anchor" :> "middle" @@ "font-family" :> "monospace" @@ 
                      "font-size" :> "12px" @@ "fill" :> text_color))
        rect == Rect(x_pos, y_pos, BUFFER_WIDTH, BUFFER_HEIGHT, 
                    ("fill" :> BufferCellColor(i) @@ "stroke" :> "#495057" @@ 
                     "stroke-width" :> "2" @@ "rx" :> "3"))
        index_label == Text(x_pos - 8, y_pos + 22, ToString(i), 
                           ("text-anchor" :> "middle" @@ "font-family" :> "monospace" @@ 
                            "font-size" :> "10px" @@ "fill" :> "#6c757d"))
    IN Group(<<rect, value, index_label>>, <<>>)

Buffer == [i \in 1..BufCapacity |-> BufferCell(i)]

\* Buffer status indicator
BufferStatus == 
    LET status_text == IF Len(buffer) = 0 THEN "EMPTY"
                      ELSE IF Len(buffer) = BufCapacity THEN "FULL"
                      ELSE ToString(Len(buffer)) \o " of " \o ToString(BufCapacity)
        x_pos == BASE_X + 150
        y_pos == BASE_Y + BufCapacity * (BUFFER_HEIGHT + CELL_SPACING) + 15
    IN Text(x_pos + 22, y_pos, status_text, 
           ("text-anchor" :> "middle" @@ "font-family" :> "monospace" @@ 
            "font-weight" :> "bold" @@ "font-size" :> "11px" @@ "fill" :> "#495057"))

\* Thread visualization helpers
ThreadColor(t) == 
    IF t \in waitSet THEN "#dc3545"  \* Bootstrap red for waiting
    ELSE "#28a745"  \* Bootstrap green for active

ThreadStatus(t) == 
    IF t \in waitSet THEN "WAIT" ELSE "RUN"

\* Consumer visualization
ConsSeq == SetToSeq(Consumers)

ConsumerCell(i) == 
    LET thread == ConsSeq[i]
        x_pos == BASE_X + 320
        y_pos == BASE_Y + (i - 1) * THREAD_SPACING
        circle == Circle(x_pos, y_pos, THREAD_RADIUS, 
                        ("fill" :> ThreadColor(thread) @@ "stroke" :> "#343a40" @@ 
                         "stroke-width" :> "2"))
        thread_label == Text(x_pos, y_pos - 3, ToString(thread), 
                            ("text-anchor" :> "middle" @@ "font-family" :> "monospace" @@ 
                             "font-size" :> "11px" @@ "font-weight" :> "bold" @@ 
                             "fill" :> "white"))
        status_label == Text(x_pos, y_pos + 8, ThreadStatus(thread), 
                            ("text-anchor" :> "middle" @@ "font-family" :> "monospace" @@ 
                             "font-size" :> "9px" @@ "fill" :> "white"))
    IN Group(<<circle, thread_label, status_label>>, <<>>)

Conss == [i \in 1..Cardinality(Consumers) |-> ConsumerCell(i)]

\* Producer visualization
ProdSeq == SetToSeq(Producers)

ProducerCell(i) == 
    LET thread == ProdSeq[i]
        x_pos == BASE_X
        y_pos == BASE_Y + (i - 1) * THREAD_SPACING
        circle == Circle(x_pos, y_pos, THREAD_RADIUS, 
                        ("fill" :> ThreadColor(thread) @@ "stroke" :> "#343a40" @@ 
                         "stroke-width" :> "2"))
        thread_label == Text(x_pos, y_pos - 3, ToString(thread), 
                            ("text-anchor" :> "middle" @@ "font-family" :> "monospace" @@ 
                             "font-size" :> "11px" @@ "font-weight" :> "bold" @@ 
                             "fill" :> "white"))
        status_label == Text(x_pos, y_pos + 8, ThreadStatus(thread), 
                            ("text-anchor" :> "middle" @@ "font-family" :> "monospace" @@ 
                             "font-size" :> "9px" @@ "fill" :> "white"))
    IN Group(<<circle, thread_label, status_label>>, <<>>)

Prod == [i \in 1..Cardinality(Producers) |-> ProducerCell(i)]

\* Section labels
ProducerLabel == Text(BASE_X, BASE_Y - 30, "PRODUCERS", 
                     ("text-anchor" :> "middle" @@ "font-family" :> "monospace" @@ 
                      "font-weight" :> "bold" @@ "font-size" :> "12px" @@ 
                      "fill" :> "#495057"))

ConsumerLabel == Text(BASE_X + 320, BASE_Y - 30, "CONSUMERS", 
                     ("text-anchor" :> "middle" @@ "font-family" :> "monospace" @@ 
                      "font-weight" :> "bold" @@ "font-size" :> "12px" @@ 
                      "fill" :> "#495057"))

BufferLabel == Text(BASE_X + 172, BASE_Y - 30, "BUFFER", 
                   ("text-anchor" :> "middle" @@ "font-family" :> "monospace" @@ 
                    "font-weight" :> "bold" @@ "font-size" :> "12px" @@ 
                    "fill" :> "#495057"))

\* Flow arrows
FlowArrows == 
    LET arrow1 == Text(BASE_X + 105, BASE_Y + 10, "→", 
                      ("text-anchor" :> "middle" @@ "font-size" :> "18px" @@ 
                       "fill" :> "#6c757d"))
        arrow2 == Text(BASE_X + 245, BASE_Y + 10, "→", 
                      ("text-anchor" :> "middle" @@ "font-size" :> "18px" @@ 
                       "fill" :> "#6c757d"))
    IN Group(<<arrow1, arrow2>>, <<>>)

\* Step number in bottom-right corner
StepNumber == 
    Text(550, 340, "Step " \o ToString(TLCGet("level")), 
         ("text-anchor" :> "end" @@ "font-size" :> "12px" @@ 
          "font-family" :> "monospace" @@ "fill" :> "#666"))

AnimView == 
    Group(<<ProducerLabel, BufferLabel, ConsumerLabel, BufferStatus, FlowArrows, StepNumber>> \o 
          Prod \o Buffer \o Conss, <<>>)

AnimDoc == SVGDoc(AnimView, 0, 0, 560, 350, <<>>)

AnimAlias ==
    [buffer |-> buffer, waitSet |-> waitSet] @@
    [_anim |-> SVGSerialize(AnimDoc, "BlockingQueue_anim_", TLCGet("level"))]

AnimWatch ==
    SVGSerialize(AnimDoc, "BlockingQueue_anim", 0)
====
```

**Key Techniques:**
- Color-coded thread states (green=running, red=waiting)
- Buffer visualization with empty/full slots and content display
- Professional layout with labeled sections
- Status indicators showing buffer capacity
- Flow arrows showing data movement direction

### 3. River Crossing Puzzle (`CabbageGoatWolf_anim.tla`)

Classic puzzle with interactive elements showing the farmer, cabbage, goat, and wolf.

**Original specification**: [`CabbageGoatWolf.tla`](https://github.com/will62794/spectacle/tree/master/specs/CabbageGoatWolf.tla)  
**Example animation**: [`CabbageGoatWolf_anim.svg`](https://github.com/will62794/spectacle/tree/master/specs/CabbageGoatWolf_anim.svg)

```tla
---- MODULE CabbageGoatWolf_anim ----
EXTENDS TLC, SVG, SequencesExt, Functions, CabbageGoatWolf

ActorIcon == (
    W :> "assets/wolf-svgrepo-com.svg" @@
    C :> "assets/cabbage-svgrepo-com.svg" @@
    G :> "assets/goat-svgrepo-com.svg" @@
    F :> "assets/farmer-svgrepo-com.svg"
)
BoatIcon == "assets/boat-svgrepo-com.svg"
RiverIcon == "assets/river-svgrepo-com.svg"
DangerIcon == "assets/danger-svgrepo-com.svg"
SuccessIcon == "assets/check-mark-button-svgrepo-com.svg"

Actors == {C, G, W, F}
ActorsOnSide(side) == {a \in Actors : a \in banks[side]}

actorWidth == 25
ActorElem(side, actor, order) == 
    IF side = 3  \* In boat
    THEN Image(80, order*35, actorWidth, actorWidth, ActorIcon[actor], <<>>)
    ELSE Image((side-1)*140, order*35, actorWidth, actorWidth, ActorIcon[actor], <<>>)

\* Display danger icon if animals are left alone in unsafe configuration
DangerElem(side) == 
    Image((side-1)*140, 0, 30, 30, DangerIcon, 
          [hidden |-> IF Allowed(banks[side]) THEN "hidden" ELSE "visible"])

SuccessElem(side) == 
    Image((side-1)*145, 0, 13, 13, SuccessIcon, 
          IF NotSolved THEN [hidden |-> "true"] ELSE <<>>)

SideElem(side) == 
    Group(SetToSeq({ 
        LET order == CHOOSE f \in [ActorsOnSide(side) -> 1..Cardinality(ActorsOnSide(side))] : 
                     IsInjective(f) 
        IN ActorElem(side, a, order[a]) : a \in ActorsOnSide(side)
    }) \o <<DangerElem(side)>>, [i \in {} |-> {}])

BoatActorElems == 
    Group(SetToSeq({
        LET order == CHOOSE f \in [boat -> 1..Cardinality(boat)] : 
                     IsInjective(f) 
        IN ActorElem(3, a, order[a]) : a \in boat
    }), [i \in {} |-> {}])
    
BoatElem == 
    Group(<<BoatActorElems>>, [i \in {} |-> {}])

RiverElem == 
    Image(55, 5, 80, 80, RiverIcon, 
          [style |-> "opacity:0.3;transform:scale(1,1.75); /* W3C */"])

AnimView == 
    Group(<<SideElem(1), SideElem(2), SuccessElem(2), RiverElem, BoatElem>>, <<>>)

AnimDoc == SVGDoc(AnimView, 0, 0, 530, 420, <<>>)

AnimAlias ==
    [banks |-> banks, boat |-> boat] @@
    [_anim |-> SVGSerialize(AnimDoc, "CabbageGoatWolf_anim_", TLCGet("level"))]

AnimWatch ==
    SVGSerialize(AnimDoc, "CabbageGoatWolf_anim", 0)
====
```

**Key Techniques:**
- Icon-based visualization using external SVG assets
- State validation with danger indicators (red warning when goat+cabbage or goat+wolf alone)
- Conditional visibility using hidden attribute
- Success celebration when puzzle is solved
- Spatial organization with river between banks
- Boat visualization showing current passengers

### 4. Dining Philosophers (`DiningPhilosophers_anim.tla`)

Classic concurrency problem with philosophers and forks arranged in a circle.

**Original specification**: [`DiningPhilosophers.tla`](https://github.com/will62794/spectacle/tree/master/specs/DiningPhilosophers.tla)  
**Example animation**: [`DiningPhilosophers_anim.svg`](https://github.com/will62794/spectacle/tree/master/specs/DiningPhilosophers_anim.svg)

```tla
---- MODULE DiningPhilosophers_anim ----
EXTENDS TLC, SVG, DiningPhilosophers

\* Predefined coordinates for circular arrangement (5 philosophers)
Coords ==
  1 :> [x |-> 100, y |-> 50] @@  \* Top
  2 :> [x |-> 70, y |-> 120] @@  \* Bottom-right
  3 :> [x |-> 10, y |-> 100] @@  \* Bottom-left
  4 :> [x |-> 10, y |-> 20]  @@  \* Top-left
  5 :> [x |-> 70, y |-> 0]   @@  \* Top-right
  \* Fork positions (between philosophers)
  7 :> [x |-> 85, y |-> 85]  @@ \* Between 1 and 2
  8 :> [x |-> 40, y |-> 110] @@ \* Between 2 and 3
  9 :> [x |-> 10, y |-> 60]  @@ \* Between 3 and 4
 10 :> [x |-> 40, y |-> 10]  @@ \* Between 4 and 5
  6 :> [x |-> 85, y |-> 25]     \* Between 5 and 1

F1 == "assets/fork-svgrepo-com.svg"
F2 == "assets/fork-food-kitchen-svgrepo-com.svg"

RingPhil == 
    [n \in P |-> Group(<<
        \* Philosopher shape - square when waiting, round when eating
        Rect(Coords[n].x, Coords[n].y, 20, 20,
            [rx |-> IF IsEating(n) THEN "0" ELSE "15", 
             stroke |-> "black", opacity |-> "0.3", fill |-> "black"]),
        \* Number label (hidden when holding forks)
        Text(Coords[n].x + 10, Coords[n].y + 15, ToString(n), 
            ("fill" :> "black" @@ "text-anchor" :> "middle" @@ 
             IF philosophers[n] # {} THEN [hidden |-> "true"] ELSE <<>>)),
        \* Fork icon when holding one fork
        Image(Coords[n].x, Coords[n].y, 20, 20, F1, 
              IF Cardinality(philosophers[n]) \in {1,2} THEN <<>> 
              ELSE [hidden |-> "true"]),
        \* Different fork icon when holding two forks (eating)
        Image(Coords[n].x, Coords[n].y, 20, 20, F2, 
              IF Cardinality(philosophers[n]) = 2 THEN <<>> 
              ELSE [hidden |-> "true"])
    >>, <<>>)]

\* Fork placement between philosophers
RingFork == 
    [n \in P |-> 
        Image(Coords[n+5].x, Coords[n+5].y, 20, 20, F1, 
              IF n \in forks THEN <<>> ELSE [hidden |-> "true"])]

AnimView ==
    Group(RingPhil \o RingFork, <<>>)

AnimDoc == SVGDoc(AnimView, 0, 0, 270, 270, <<>>)

AnimAlias ==
    [philosophers |-> philosophers, forks |-> forks] @@
    [_anim |-> SVGSerialize(AnimDoc, "DiningPhilosophers_anim_", TLCGet("level"))]

AnimWatch ==
    SVGSerialize(AnimDoc, "DiningPhilosophers_anim", 0)
====
```

**Key Techniques:**
- Predefined coordinate mapping for circular table layout
- Shape morphing (rounded corners when thinking, square when eating)
- Multiple visual states: no forks, one fork, two forks (eating)
- Conditional visibility for fork placement
- Icon changes based on philosopher state
- Clean visual representation of the classic deadlock problem

### 5. Two-Phase Commit (`TwoPhase_anim.tla`)

Distributed transaction protocol with resource managers and transaction manager.

**Original specification**: [`TwoPhase.tla`](https://github.com/will62794/spectacle/tree/master/specs/TwoPhase.tla)  
**Example animation**: [`TwoPhase_anim.svg`](https://github.com/will62794/spectacle/tree/master/specs/TwoPhase_anim.svg)

```tla
------------------------------- MODULE TwoPhase_anim ----------------------------- 
EXTENDS TLC, Naturals, Sequences, Functions, FiniteSets, SVG, TwoPhase

CommitColor == "green"
AbortColor == "red"

\* Establish deterministic ordering for resource managers
RMId == CHOOSE f \in [1..Cardinality(RM) -> RM] : IsInjective(f)
RMIdDomain == 1..Cardinality(RM)

\* RM elements - circular nodes with state-based colors
RMSpacing == 40
RMElems == [i \in RMIdDomain |-> 
    Circle(RMSpacing * i, 45, 10, 
        [stroke |-> "black", fill |-> 
            IF rmState[RMId[i]] = "prepared" THEN "steelblue" 
            ELSE IF rmState[RMId[i]] = "committed" THEN CommitColor 
            ELSE IF rmState[RMId[i]] = "aborted" THEN AbortColor 
            ELSE "gray"])]

\* Transaction Manager positioned at center
TMXpos == RMSpacing * ((Cardinality(RM) + 1) \div 2)
TMElem == Circle(TMXpos, 95, 10, 
    [stroke |-> "black", 
     fill |-> IF tmState = "committed" THEN CommitColor 
              ELSE IF tmState = "init" THEN "gray" 
              ELSE AbortColor])

\* RM labels showing their names
RMTextElems == 
    [i \in RMIdDomain |->
        Text(40 * i, 30, RMId[i], 
             ("fill" :> "black" @@ "text-anchor" :> "middle" @@ 
              "font-size" :> "12"))
    ]

\* TM label and prepared set display
TMTextElems == <<
    Text(TMXpos, 80, "TM", 
         ("fill" :> "black" @@ "text-anchor" :> "middle" @@ 
          "font-size" :> "12")),
    Text(TMXpos, 120, ToString(tmPrepared), 
         ("fill" :> "black" @@ "text-anchor" :> "middle" @@ 
          "font-size" :> "10"))
>>

TextElems == RMTextElems \o TMTextElems

AnimView == 
    Group(RMElems \o <<TMElem>> \o TextElems, <<>>)

AnimDoc == SVGDoc(AnimView, 0, 0, 180, 200, <<>>)

AnimAlias ==
    [rmState |-> rmState, tmState |-> tmState, 
     tmPrepared |-> tmPrepared, msgs |-> msgs] @@
    [_anim |-> SVGSerialize(AnimDoc, "TwoPhase_anim_", TLCGet("level"))]

AnimWatch ==
    SVGSerialize(AnimDoc, "TwoPhase_anim", 0)
=============================================================================
```

**Key Techniques:**
- State-based color coding (gray=working, blue=prepared, green=committed, red=aborted)
- Dynamic positioning based on number of resource managers
- Hierarchical layout with RMs on top, TM below
- Set visualization showing which RMs have prepared
- Clean visual representation of distributed consensus

### 6. MongoDB Raft Reconfiguration (`MongoRaftReconfig_anim.tla`)

Complex distributed consensus with log replication and dynamic reconfiguration.

**Original specification**: [`MongoRaftReconfig.tla`](https://github.com/will62794/spectacle/tree/master/specs/MongoRaftReconfig.tla)  
**Example animation**: [`MongoRaftReconfig_anim.svg`](https://github.com/will62794/spectacle/tree/master/specs/MongoRaftReconfig_anim.svg)

```tla
---- MODULE MongoRaftReconfig_anim ----
EXTENDS SVG, SequencesExt, MongoRaftReconfig

Spacing == 40
CrownIcon == "assets/crown.svg"
BugIcon == "assets/bug.svg"

\* Deterministic ordering for servers
RMId == SetToSeq(Server)
RMIdDomain == 1..Cardinality(Server)
XBase == -15

\* Log entry visualization with commit status highlighting
logEntryStyle(i,ind) == 
    IF \E c \in immediatelyCommitted : c[1] = ind /\ c[2] = log[i][ind] 
        THEN ("fill" :> "lightgray" @@ "stroke" :> "limegreen" @@ 
              "stroke-width" :> "1.5px")
        ELSE ("fill" :> "lightgray" @@ "stroke" :> "black" @@ 
              "stroke-width" :> "1px")

logEntry(i, ybase, ind) == 
    Group(<<Rect(18 * ind + 140, ybase, 16, 16, logEntryStyle(i,ind)), 
            Text(18 * ind + 145, ybase + 12, ToString(log[i][ind]), 
                 ("text-anchor" :> "start" @@ "font-size" :> "10px"))>>, 
          [h \in {} |-> {}])

logElem(i, ybase) == 
    Group([ind \in DOMAIN log[i] |-> logEntry(i, ybase, ind)], 
          [h \in {} |-> {}])

logElems == [i \in RMIdDomain |-> logElem(RMId[i], i * Spacing - 9)]

\* Server visualization with role-based colors
cs == [i \in RMIdDomain |-> 
    Group(<<
        Circle(XBase + 20, i * Spacing, 10, 
            [stroke |-> "black", fill |-> 
                IF state[RMId[i]] = Primary THEN "gold" 
                ELSE IF state[RMId[i]] = Secondary THEN "gray" 
                ELSE "lightgray"]),
        CrownElem(XBase-10, RMId[i], i)
    >>, [h \in {} |-> {}])]

\* Leader crown indicator
CrownElem(xbase, rmid, i) == 
    Image(xbase, i * Spacing - 6, 13, 13, CrownIcon, 
          IF state[rmid] # Primary THEN [hidden |-> "true"] ELSE <<>>)

\* Configuration and term information
configStr(rmid) == ToString(config[rmid])
configVersionAndTermStr(rmid) == 
    "(" \o ToString(configVersion[rmid]) \o ", " \o 
    ToString(configTerm[rmid]) \o ")"

labelText(i, rmid) == 
    Group(<<
        Text(XBase + 38, i * Spacing + 5, 
            ToString(rmid) \o "     " \o configStr(rmid), 
            [fill |-> IF state[rmid] = Primary THEN "black" 
                     ELSE IF state[rmid] = Secondary THEN "black" 
                     ELSE "gray"] @@ 
            ("font-family" :> "monospace" @@ "font-size" :> "8px")),
        Text(XBase + 130, i * Spacing + 5, configVersionAndTermStr(rmid), 
            ("fill" :> "black" @@ "font-family" :> "monospace" @@ 
             "font-size" :> "6px"))
    >>, [h \in {} |-> {}])

labels == [i \in RMIdDomain |-> labelText(i, RMId[i])]

\* Term visualization
termLabels == 
    [i \in RMIdDomain |-> 
        Group(<<
            Text(XBase + 38 + currentTerm[RMId[i]] * 11, i * Spacing + 20, 
                ToString(currentTerm[RMId[i]]), 
                [fill |-> IF state[RMId[i]] = Primary THEN "black" 
                         ELSE IF state[RMId[i]] = Secondary THEN "black" 
                         ELSE "gray"] @@ 
                ("font-family" :> "monospace" @@ "font-size" :> "7px")),
            Text(XBase + 10, i * Spacing + 20, "term:", 
                [fill |-> IF state[RMId[i]] = Primary THEN "black" 
                         ELSE IF state[RMId[i]] = Secondary THEN "black" 
                         ELSE "gray"] @@ 
                ("font-family" :> "monospace" @@ "font-size" :> "7px")),
            Rect(XBase + 35, i * Spacing + 20, 100, 1, [fill |-> "white"])
        >>, <<>>)]

\* Safety violation detection
existsConflictingEntry(ind) == 
    \E x,y \in immediatelyCommitted : 
        x[1] = ind /\ (x[1] = y[1]) /\ x[2] # y[2]

violationEntry(ybase, ind) == 
    Image(16 * ind + 115, ybase + 9, 13, 13, BugIcon, 
          IF existsConflictingEntry(ind) THEN <<>> ELSE [hidden |-> "true"])

violationElem(ybase) == 
    Group([ind \in 1..5 |-> violationEntry(ybase, ind)], <<>>)

safetyViolationElems == <<violationElem(5)>>

\* Title labels
configVersionTermTitleLabel == 
    <<Text(100, 20, "(version, term)", 
           ("fill" :> "black" @@ "font-family" :> "monospace" @@ 
            "font-size" :> "6px"))>>

\* Complete animation view
AnimView == 
    Group(cs \o labels \o termLabels \o logElems \o 
          safetyViolationElems \o configVersionTermTitleLabel, <<>>)

AnimDoc == SVGDoc(AnimView, 0, 0, 720, 350, <<>>)

AnimAlias ==
    [currentTerm |-> currentTerm, state |-> state, log |-> log, 
     immediatelyCommitted |-> immediatelyCommitted, config |-> config, 
     configVersion |-> configVersion, configTerm |-> configTerm] @@
    [_anim |-> SVGSerialize(AnimDoc, "MongoRaftReconfig_anim_", TLCGet("level"))]

AnimWatch ==
    SVGSerialize(AnimDoc, "MongoRaftReconfig_anim", 0)
=============================================================================
```

**Key Techniques:**
- Log replication visualization with entry-by-entry display
- Commit status highlighting (green border for committed entries)
- Leader election indicators (crown icon)
- Configuration version and term tracking
- Safety violation detection (bug icon appears on conflicts)
- Complex state display including server configs
- Term progression visualization
- Professional layout with multiple information layers

### Common Patterns Across Examples

1. **Deterministic Ordering**: All examples use `SetToSeq` for consistent element ordering
2. **State-Based Styling**: Colors, shapes, and visibility change based on state
3. **Icon Integration**: External SVG assets for intuitive representation
4. **Conditional Visibility**: Using `hidden` attribute for dynamic elements
5. **Layout Calculations**: Mathematical positioning for organized displays
6. **Grouped Elements**: Logical grouping of related visual components
7. **Text Overlays**: State information displayed as text labels
8. **Step Number Display**: Every frame includes `TLCGet("level")` for progression tracking

These examples demonstrate the full range of TLA+ animation capabilities, from simple state indicators to complex distributed system visualizations.
