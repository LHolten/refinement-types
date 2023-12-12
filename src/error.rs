use crate::refinement::builtin::builtins;

pub struct MultiFile {
    builtin: Vec<&'static str>,
    code: String,
}

impl MultiFile {
    pub fn new(code: String) -> Self {
        Self {
            builtin: builtins(),
            code,
        }
    }
}

impl miette::SourceCode for MultiFile {
    fn read_span<'a>(
        &'a self,
        span: &miette::SourceSpan,
        context_lines_before: usize,
        context_lines_after: usize,
    ) -> Result<Box<dyn miette::SpanContents<'a> + 'a>, miette::MietteError> {
        let mut start = 0;
        let mut code = &*self.code;
        for b in &self.builtin {
            if span.offset() < start + b.len() {
                code = b;
                break;
            }
            start += b.len();
        }

        let local_span = &(span.offset() - start, span.len()).into();
        let local = code.read_span(local_span, context_lines_before, context_lines_after)?;

        let local_span = local.span();
        let span = (local_span.offset() + start, local_span.len()).into();

        Ok(Box::new(miette::MietteSpanContents::new(
            local.data(),
            span,
            local.line(),
            local.column(),
            local.line_count(),
        )))
    }
}
