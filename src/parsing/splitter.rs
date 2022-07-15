use super::*;

const LINE_START_PATS: &'static [&'static str] = &["where", "else", ")", ":"];

pub fn split(db: &dyn Parser, file: File) -> Vec<TextSplit> {
    let source = db.input_file(file);

    let mut names = HashMap::new();
    let mut psplits = Vec::new();
    let mut next_started = false;
    let mut split_start = 0;
    let mut byte_pos = 0;
    'next_line: for line in source.lines() {
        byte_pos += line.len_bytes();
        match line.chars().next() {
            // Attach to previous split
            None => {
                if !next_started && split_start != 0 {
                    split_start = byte_pos;
                }
            }
            Some(x) if x.is_whitespace() => {
                if !next_started && split_start != 0 {
                    split_start = byte_pos;
                }
            }
            // Attach to next split
            Some('#' | '@') => next_started = true,
            // Start a new split
            _ => {
                for pat in LINE_START_PATS {
                    if line.len_bytes() > pat.len() {
                        let sub = line.slice(0..pat.len());
                        let matches = if let Some(sub) = sub.as_str() {
                            sub == *pat
                        } else {
                            sub.chars().zip(pat.chars()).all(|(x, y)| x == y)
                        };
                        if matches {
                            if !next_started && split_start != 0 {
                                split_start = byte_pos;
                            }
                            continue 'next_line;
                        }
                    }
                }
                next_started = false;
                if split_start != 0 {
                    psplits.push(split_start);
                }
                split_start = byte_pos;
            }
        }
    }
    psplits.push(byte_pos);

    let mut splits = Vec::new();
    byte_pos = 0;
    let mut start_line = 0;
    for i in psplits {
        let text: Rope = source.byte_slice(byte_pos..i).into();
        let lines = text.len_lines() - 1;

        let mut name = None;
        for i in text.lines() {
            let words = i.to_string();
            let mut words = words.split_whitespace().peekable();
            if words.peek() == Some(&"pub") {
                words.next();
            }
            if matches!(words.next(), Some("fun" | "let" | "eff" | "type")) {
                name = words
                    .next()
                    .map(|x| {
                        x.chars()
                            .take_while(|x| x.is_alphanumeric() || *x == '_')
                            .collect()
                    })
                    .map(|x| db.name(x))
                    // For duplicate definition names in the same file, use `a`, `a'2`, `a'3` etc.
                    // so they have different `SplitLoc`s
                    .map(|x| match names.entry(x) {
                        std::collections::hash_map::Entry::Occupied(mut e) => {
                            let e = e.get_mut();
                            *e += 1;
                            db.name(format!("{}'{}", db.lookup_name(x), *e))
                        }
                        std::collections::hash_map::Entry::Vacant(e) => {
                            e.insert(1);
                            x
                        }
                    });
                break;
            }
        }

        splits.push(TextSplit {
            name,
            start_line,
            abs_span: AbsSpan(file, byte_pos as u32..i as u32),
            text,
        });
        byte_pos = i;
        start_line += lines;
    }

    splits
}
