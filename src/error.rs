use std::{error::Error, fmt::Display, fs, process::exit};

use miette::{Diagnostic, LabeledSpan, Report};

use crate::refinement::builtin::builtins;

#[derive(Clone)]
pub struct MultiFile {
    pub builtin: Vec<&'static str>,
    pub code: String,
    pub path: String,
}

impl MultiFile {
    pub fn new(path: &str) -> Self {
        Self {
            builtin: builtins(),
            code: fs::read_to_string(path).unwrap(),
            path: path.to_owned(),
        }
    }

    pub fn offset(&self) -> usize {
        self.builtin.iter().map(|x| x.len()).sum()
    }

    pub fn unwrap<T, E: Diagnostic + Send + Sync + 'static>(&self, res: Result<T, E>) -> T {
        match res {
            Ok(val) => val,
            Err(e) => {
                let report = Report::from(e);
                let e = report.with_source_code(self.to_owned());
                println!("{e:?}");
                exit(1)
            }
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
        let mut header = self.path.as_str();
        for b in &self.builtin {
            if span.offset() < start + b.len() {
                code = b;
                header = "builtin";
                break;
            }
            start += b.len();
        }

        let local_span = &(span.offset() - start, span.len()).into();
        let local = code.read_span(local_span, context_lines_before, context_lines_after)?;

        let local_span = local.span();
        let span = (local_span.offset() + start, local_span.len()).into();

        Ok(Box::new(miette::MietteSpanContents::new_named(
            header.to_owned(),
            local.data(),
            span,
            local.line(),
            local.column(),
            local.line_count(),
        )))
    }
}

#[derive(Debug)]
pub struct AppendLabels {
    pub prefix: &'static str,
    pub inner: Box<dyn Diagnostic + Send + Sync>,
    pub extra: Vec<LabeledSpan>,
}

impl Display for AppendLabels {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.prefix)?;
        self.inner.fmt(f)
    }
}

impl Error for AppendLabels {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        self.inner.source()
    }
}

impl Diagnostic for AppendLabels {
    fn code<'a>(&'a self) -> Option<Box<dyn std::fmt::Display + 'a>> {
        self.inner.code()
    }

    fn severity(&self) -> Option<miette::Severity> {
        self.inner.severity()
    }

    fn help<'a>(&'a self) -> Option<Box<dyn std::fmt::Display + 'a>> {
        self.inner.help()
    }

    fn url<'a>(&'a self) -> Option<Box<dyn std::fmt::Display + 'a>> {
        self.inner.url()
    }

    fn source_code(&self) -> Option<&dyn miette::SourceCode> {
        self.inner.source_code()
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = LabeledSpan> + '_>> {
        Some(Box::new(
            self.inner
                .labels()
                .into_iter()
                .flatten()
                .chain(self.extra.clone()),
        ))
    }

    fn related<'a>(&'a self) -> Option<Box<dyn Iterator<Item = &'a dyn Diagnostic> + 'a>> {
        self.inner.related()
    }

    fn diagnostic_source(&self) -> Option<&dyn Diagnostic> {
        self.inner.diagnostic_source()
    }
}
