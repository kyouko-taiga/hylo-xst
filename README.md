# Hylo

## Ideas for optimizations

- Store the contents of "small" type trees in the inline storage of their identities.
- Use a separate array to store the kind of each syntax tree rather than calling `kind(of:)`.
