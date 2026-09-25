---
title: How to check different TLC configurations
description: Learn how to validate TLA+ models by running TLC with multiple configurations of constant values, ensuring broader coverage and avoiding missed corner cases while managing state-space explosion.
---

## How to check different TLC configurations

### Check models across combinations of constant values

When using CONSTANT declarations in your TLA+ model, ensure the model is verified with multiple TLC configuration (.cfg) files, each specifying a different combination of constant values. Always start with the smallest possible configuration, then gradually increase the configuration size. Keep in mind that even a linear increase in configuration size can lead to exponential (or greater) growth in the state space, a phenomenon known as state-space explosion.

### Rationale

- A single constant assignment may not expose corner cases.
- Meaningful coverage requires checking a variety of constant combinations that reflect real-world or extreme scenarios.
