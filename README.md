# Hylo

## Misc

Nested types can only be declared in primary declaration.
- Simplifies qualified name lookup because extensions cannot define new nested types.
- Makes sense in the context of scoped conformances because the definition of a type in an extension may break someone else's code. (not so compelling because of properties?)

## Ideas for optimizations

- Store the contents of "small" type trees in the inline storage of their identities.
- Use a separate array to store the kind of each syntax tree rather than calling `kind(of:)`.
