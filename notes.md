# TRIVIA/CONCRETE SYNTAX STUFF
so we need to be able to refactor things with access to types
Three options for that:
1. No desugaring, Term includes the entire concrete syntax of the language and is tagged with trivia
2. Desugaring but Term has tags for what desugaring happened and how to reverse it
3. Perform the refactoring on Pre but with some information from elaboration
I think 3 makes the most sense
For right now, all we need to know is where trivia goes
and we'll need it on Pre anyway
