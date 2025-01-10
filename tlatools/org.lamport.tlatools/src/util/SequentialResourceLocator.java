// Copyright (c) 2025, Oracle and/or its affiliates.

package util;

import java.io.IOException;
import java.net.URL;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Tries several other locators in sequence.  The first found result is returned.
 */
class SequentialResourceLocator implements ResourceLocator {

    private final List<ResourceLocator> locators;

    public SequentialResourceLocator(List<ResourceLocator> locators) {
        this.locators = locators;
    }

    @Override
    public URL locate(String filename) throws IOException {
        for (ResourceLocator locator : locators) {
            URL found = locator.locate(filename);
            if (found != null) {
                return found;
            }
        }
        return null;
    }

    @Override
    public String describeSearchLocations() {
        return locators.stream().map(ResourceLocator::describeSearchLocations).collect(Collectors.joining(", "));
    }

}
