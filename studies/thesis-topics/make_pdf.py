"""Builds thesis_topics.pdf: the master thesis proposal "Correlated credibility: extensions, tested on card
data" (notes/card-data.md, Step 8). It is the thesis worker's main document. Written for a student who
knows neither the 2023 thesis nor the repository: each extension says what to derive, and points to
the handbook (formula and proof idea) to check against. Handbook numbers are read from
handbook/handbook.tex at build time.
Edit this script, not the PDF, and rerun it: python3 make_pdf.py (needs reportlab)."""
from reportlab.lib.pagesizes import A4
from reportlab.platypus import (SimpleDocTemplate, Paragraph, Spacer, ListFlowable, ListItem,
                                Table, TableStyle, KeepTogether)
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib.units import cm
from reportlab.lib import colors

# FreeSans covers the math glyphs Helvetica lacks (the hat in μ̂, ≻, ℓ); Helvetica as a fallback.
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.lib.fonts import addMapping

# reportlab puts the first non-ASCII characters of a TrueType subset at codes 1-31 (tab, line feed,
# carriage return, ...). Many phone and Mac viewers draw those as black boxes. Start them at 128.
_state_init = TTFont.State.__init__
def _state_init_above_ascii(self, asciiReadable=None, ttf=None):
    _state_init(self, asciiReadable, ttf)
    if not self.frozen and self.nextCode == 1 and len(self.subsets[0]) == 128:
        self.nextCode = 128
TTFont.State.__init__ = _state_init_above_ascii

# reportlab shifts sub- and superscripts by half the font size, so subscripts touch the next line.
# Use the usual typeset shifts (about a quarter down, a third up).
import reportlab.platypus.paraparser as _pp
_pp.subFraction, _pp.supFraction = 0.24, 0.36

_dv = "/usr/share/fonts/truetype/freefont/"
try:
    for name, f in [("DV", "FreeSans.ttf"), ("DV-B", "FreeSansBold.ttf"),
                    ("DV-I", "FreeSansOblique.ttf"), ("DV-BI", "FreeSansBoldOblique.ttf")]:
        pdfmetrics.registerFont(TTFont(name, _dv + f))
    addMapping("DV", 0, 0, "DV"); addMapping("DV", 1, 0, "DV-B"); addMapping("DV", 0, 1, "DV-I"); addMapping("DV", 1, 1, "DV-BI")
    SANS, SANS_B, SANS_I = "DV", "DV-B", "DV-I"
except Exception as e:
    print('fonts: falling back to Helvetica:', e)
    SANS, SANS_B, SANS_I = "Helvetica", "Helvetica-Bold", "Helvetica-Oblique"

out = "thesis_topics.pdf"
doc = SimpleDocTemplate(out, pagesize=A4, leftMargin=2.3*cm, rightMargin=2.3*cm,
                        topMargin=1.8*cm, bottomMargin=1.8*cm,
                        title="Master Thesis Proposal: Correlated Credibility, Extensions Tested on Card Data (draft v3)")
ss = getSampleStyleSheet()
NAVY = colors.HexColor("#1f3a5f")
title = ParagraphStyle("T", parent=ss["Title"], fontName=SANS_B, fontSize=17, leading=21, spaceAfter=2)
sub = ParagraphStyle("S", parent=ss["Normal"], fontName=SANS_I, fontSize=10, textColor=colors.grey, alignment=1, spaceAfter=12)
h = ParagraphStyle("H", parent=ss["Heading2"], fontName=SANS_B, fontSize=12, spaceBefore=9, spaceAfter=3, textColor=NAVY)
h3 = ParagraphStyle("H3", parent=ss["Normal"], fontName=SANS_B, fontSize=10.3, spaceBefore=6, spaceAfter=2)
body = ParagraphStyle("B", parent=ss["Normal"], fontName=SANS, fontSize=9.6, leading=13.4)
ref = ParagraphStyle("R", parent=body, fontSize=9.3, leading=12.2)
cell = ParagraphStyle("C", parent=body, fontSize=9.2, leading=12)
lean = ParagraphStyle("L", parent=body, fontSize=8.8, leading=11.5, textColor=colors.HexColor("#444444"), leftIndent=0)


def bullets(items, numbered=False, style=body):
    return ListFlowable([ListItem(Paragraph(i, style), leftIndent=14) for i in items],
                        bulletType="1" if numbered else "bullet",
                        leftIndent=16, bulletFontSize=10)


def code(*names):
    return ", ".join(f"<font face='Courier' size='8.3'>{n}</font>" for n in names)


def table(rows, widths):
    t = Table([[Paragraph(c, cell) for c in r] for r in rows], colWidths=widths, repeatRows=1)
    t.setStyle(TableStyle([
        ("LINEBELOW", (0, 0), (-1, 0), 0.6, NAVY),
        ("LINEBELOW", (0, 1), (-1, -1), 0.25, colors.lightgrey),
        ("VALIGN", (0, 0), (-1, -1), "TOP"),
        ("TOPPADDING", (0, 0), (-1, -1), 3), ("BOTTOMPADDING", (0, 0), (-1, -1), 4),
    ]))
    return t


SITE = "https://mikaelandblom-coder.github.io/credible-lean/"
THESIS = ("Andblom, M. (2023). <i>Generalized B&uuml;hlmann&ndash;Straub credibility theory for "
          "correlated data</i>. Master Thesis in Actuarial Mathematics 2023:2, Stockholm University.")
# The thesis cites a frozen release; fill in its version DOI from Zenodo once v3.0.0 is out.
VERSION, VERSION_DOI = "v3.0.0", "10.5281/zenodo.24054631"  # TODO: v3.0.0 version DOI
REPO = ("<i>credible-lean: a Lean 4 formalization of correlated credibility theory</i>, " + VERSION +
        " (2026). doi:" + VERSION_DOI + ". All repository paths in this proposal refer to this release. "
        "Current site (keeps developing): " + SITE + " (paper, handbook, app, blueprint).")
BG = ("B&uuml;hlmann, H. and Gisler, A. (2005). <i>A Course in Credibility Theory and its Applications</i>. "
      "Springer (chapters 4, 8 and 9).")

s = []

# ---------------------------------------------------------------- handbook numbers
import os, re
_hb = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "handbook", "handbook.tex")).read()
_labels = re.findall(r"\\begin\{result\}(?:\[[^\n]*?\])?\s*\\label\{(res:[^}]*)\}", _hb)
_num = {lab: i + 1 for i, lab in enumerate(_labels)}


def H(*labels):
    """'Handbook 31' or 'Handbook 31, 32' (a range for consecutive numbers)."""
    ns = sorted(_num[l] for l in labels)  # KeyError: a label was renamed in the handbook
    if len(ns) > 1 and ns == list(range(ns[0], ns[-1] + 1)) and len(ns) > 2:
        return f"Handbook {ns[0]}&ndash;{ns[-1]}"
    return "Handbook " + ", ".join(str(n) for n in ns)


def _cap(t):
    return t[0].upper() + t[1:] if t[:1].islower() else t


def ext(name, idea, model, derive, data, where, size):
    model, data = _cap(model), _cap(data)
    return KeepTogether([
        Paragraph(name, h3),
        Paragraph("<i>Idea.</i> " + idea, body),
        Paragraph("<i>A suggested model.</i> " + model, body),
        Paragraph("<i>Derive.</i>", body),
        bullets(derive, numbered=True),
        Paragraph("<i>Data question.</i> " + data, body),
        Paragraph("<i>Check against:</i> " + where + " &middot; <i>Size:</i> " + size, lean),
    ])


mu_hat = "&mu;&#770;"
s = []

# ---------------------------------------------------------------- title
s.append(Paragraph("Correlated Credibility: Extensions, Tested on Card Data", title))
s.append(Paragraph("Master thesis proposal &middot; actuarial mathematics &middot; draft v3", sub))

# ---------------------------------------------------------------- 1. aim
s.append(Paragraph("1. Aim", h))
s.append(Paragraph(
    "Credibility theory prices a segment of a portfolio (a <i>cohort</i>: a region, a product, an "
    "underwriting year) from a blend of its own experience and the portfolio's. The classical "
    "B&uuml;hlmann&ndash;Straub model assumes that cohorts are independent. A master thesis "
    "(Andblom, 2023) dropped that assumption: cohorts may be correlated, as when one storm or one "
    "drop in demand hits them all. Since then the model has been extended in several directions.", body))
s.append(Spacer(1, 4))
s.append(Paragraph(
    "This thesis takes <b>two or three of those extensions</b>, derives their formulas, and tests "
    "them on real data. You derive the formulas yourself, then check them against the handbook "
    "(section 7), which states each result with the idea of its proof. Deriving is the best way to learn "
    "the subject, and it makes the thesis less dependent on mathematics generated with AI tools. The "
    "theory is general. The data are monthly claims of a travel insurance sold through payment cards "
    "(section 5), where each extension answers a concrete pricing question.", body))

# ---------------------------------------------------------------- 2. the 2023 thesis
s.append(Paragraph("2. The starting point: credibility for correlated cohorts (2023)", h))
s.append(Paragraph(
    "<b>Data.</b> Cohorts <i>j</i> = 1, &hellip;, <i>J</i> are observed in periods <i>t</i> = 1, &hellip;, "
    "<i>T</i>: a volume <i>w<sub>jt</sub></i> (e.g. vehicle-years) and an observed ratio "
    "&mu;<sub><i>jt</i></sub> (claims per unit of volume). Each cohort has a true level "
    "&mu;<sub><i>j</i></sub>, and the aim is to estimate it.", body))
s.append(Spacer(1, 3))
s.append(Paragraph(
    "<b>Model.</b> &mu;<sub><i>jt</i></sub> = &mu; + &tau;&eta;<sub><i>j</i></sub> + "
    "&sigma;<sub><i>jt</i></sub>&epsilon;<sub><i>jt</i></sub>, where &mu;<sub><i>j</i></sub> = "
    "&mu; + &tau;&eta;<sub><i>j</i></sub>. The cohort effects &eta;<sub><i>j</i></sub> and the "
    "noise &epsilon;<sub><i>jt</i></sub> are centred with unit variance, and the cohort effects are uncorrelated with each other and "
    "with the noise. The noise variance is &sigma;<sub><i>jt</i></sub>&sup2; = &sigma;<sub><i>j</i></sub>&sup2;/<i>w<sub>jt</sub></i>. "
    "The new assumption is that noise in the same period is correlated across cohorts: "
    "cov(&epsilon;<sub><i>it</i></sub>, &epsilon;<sub><i>js</i></sub>) = &rho;<sub><i>ij</i></sub>&delta;<sub><i>ts</i></sub>. "
    "Only first and second moments are assumed, no distribution. With &rho; = 0 this is "
    "B&uuml;hlmann&ndash;Straub.", body))
s.append(Spacer(1, 3))
s.append(Paragraph("<b>The recipe.</b> Every result follows from one matrix.", body))
s.append(bullets([
    f"Within a cohort, the volume-weighted mean {mu_hat}<sub><i>j</i></sub> = &Sigma;<sub><i>t</i></sub> "
    "<i>w<sub>jt</sub></i>&mu;<sub><i>jt</i></sub> / <i>w<sub>j*</sub></i> is optimal.",
    f"<i>K<sub>ij</sub></i> = cov({mu_hat}<sub><i>i</i></sub>, {mu_hat}<sub><i>j</i></sub>) = "
    "&sigma;<sub><i>i</i></sub>&sigma;<sub><i>j</i></sub>&rho;<sub><i>ij</i></sub> <i>S<sub>ij</sub></i> / "
    "(<i>w<sub>i*</sub>w<sub>j*</sub></i>) + &tau;&sup2;&delta;<sub><i>ij</i></sub>, with "
    "<i>S<sub>ij</sub></i> = &Sigma;<sub><i>t</i></sub> &radic;(<i>w<sub>it</sub>w<sub>jt</sub></i>). "
    "It must be positive definite.",
    f"The portfolio estimate {mu_hat} = &Sigma; <i>b<sub>j</sub></i>{mu_hat}<sub><i>j</i></sub> uses the "
    "GLS weights <i>b</i> = <i>K</i><sup>&minus;1</sup>1 / 1<sup>T</sup><i>K</i><sup>&minus;1</sup>1. A cohort "
    "that moves with many others gets less weight.",
    f"The blend <i>z<sub>j</sub></i>{mu_hat}<sub><i>j</i></sub> + (1 &minus; <i>z<sub>j</sub></i>){mu_hat} has "
    "the best credibility factor <i>z<sub>j</sub></i> = (1 &minus; <i>b<sub>j</sub></i>)&tau;&sup2; / "
    "(<i>K<sub>jj</sub></i> &minus; 1/1<sup>T</sup><i>K</i><sup>&minus;1</sup>1).",
    "&tau;&sup2; and &sigma;&sigma;&rho; have unbiased moment estimators, built from cross-products of "
    "deviations from the cohort means.",
], numbered=True))
s.append(Spacer(1, 3))
s.append(Paragraph(
    "Every extension below keeps steps 3&ndash;4. It changes <b>how <i>K</i> is built</b> (step 2), "
    "and sometimes what is predicted. So each extension asks for the same work: build its <i>K</i>, show "
    "that <i>K</i> is positive definite, and find estimators for the new parameters. "
    f"Handbook: the model and the recipe in section 1, steps 1&ndash;5 in {H('res:invVar', 'res:gls', 'res:z', 'res:estimation')}.", body))

# ---------------------------------------------------------------- 3. the map
s.append(Paragraph("3. Which assumptions the extensions relax", h))
s.append(table([
    ["<b>The 2023 assumption</b>", "<b>Why it can fail</b>", "<b>Extension</b>"],
    ["All cohorts observed in all periods", "Products start and stop", "E1 Entry and exit"],
    ["Correlation between cohorts falls with volume", "A demand shock hits large and small cohorts alike",
     "E2 A shock that does not shrink"],
    ["The target is a cohort's level, the predictor a blend", "One wants next year's total; better linear predictors exist",
     "E3 The best linear predictor"],
    ["One level per cohort and period", "Monthly data have a season", "E4 Season"],
    ["Periods are independent", "Demand persists over months and years", "E5 A persistent common factor"],
    ["One ratio per cohort", "Frequency and severity behave differently", "E6 Frequency and severity"],
    ["The common movement is unobserved", "A public index (e.g. passenger numbers) tracks it",
     "E7 A known demand index"],
    ["Parameters are known", "They are estimated from the same, skewed data", "E8 The price of estimation"],
], [5.4*cm, 6.0*cm, 5.0*cm]))
s.append(Spacer(1, 3))
s.append(Paragraph(
    "Each model below is a <b>suggestion</b>: you may change it if the data or the literature call for "
    "something else. Pick two or three extensions with the supervisors. Combinations that make a complete "
    "thesis are E3 + E4 (monthly data or annual totals?), E2 + E5 (what form does the correlation take, "
    "and does it persist?) and E6 + E8 (frequency and severity, estimated). E1 is small and combines with "
    "anything. Every choice also needs the method of section 4.", body))

# ---------------------------------------------------------------- the extensions
s.append(Paragraph("The extensions", h))
s.append(ext(
    "E1. Cohorts that enter and leave",
    "In 2023 every cohort was observed in every period. In practice products are launched and closed, "
    "and a closed cohort's history still says something about the others.",
    "cohort <i>j</i> is observed in the periods <i>T<sub>j</sub></i>, with the 2023 moments on the observed cells.",
    ["<i>K<sub>ij</sub></i> when correlation acts only on the periods two cohorts share.",
     "A condition for <i>K</i> &#8827; 0 that involves only cohorts observed at the same time.",
     "An unbiased estimator of &sigma;&sigma;&rho; for a pair that shares only some periods: what replaces <i>T</i> &minus; 2?"],
    "does keeping the history of closed cards improve the prediction for the open ones? The exact "
    "results assume exits unrelated to the claims. What if a card was closed for its results?",
    H("res:unequal", "res:unequal_est"), "small"))
s.append(ext(
    "E2. A common shock that does not shrink with volume",
    "In 2023 the covariance between two cohorts falls like 1/&radic;(<i>w<sub>it</sub>w<sub>jt</sub></i>): "
    "double the volume and the shared shock halves. A real shock (a storm, a drop in travel demand) hits "
    "a cohort's ratio whatever its size.",
    "cov(&mu;<sub><i>it</i></sub>, &mu;<sub><i>js</i></sub>) = &delta;<sub><i>ts</i></sub>(<i>C<sub>ij</sub></i> + "
    "&delta;<sub><i>ij</i></sub><i>s<sub>i</sub></i>&sup2;/<i>w<sub>it</sub></i>) + &tau;&sup2;&delta;<sub><i>ij</i></sub>: "
    "a period shock with covariance <i>C</i> plus process noise.",
    ["<i>K</i> for volume-weighted means, and <i>K</i> &#8827; 0.",
     "Unbiased estimators of <i>C</i> and <i>s</i>&sup2;.",
     "Why <i>s</i>&sup2; is identified only when volumes vary over time, and when this model and the 2023 model coincide."],
    "does the covariance between cards' monthly ratios shrink with volume?",
    H("res:shock", "res:shock_est"), "medium"))
s.append(ext(
    "E3. The best linear predictor of any target",
    "The blend is one linear predictor among many, and it targets the level &mu;<sub><i>j</i></sub>. "
    "A price is for next year's total, and the best predictor may weight each cohort separately.",
    "data <i>x</i> with covariance <i>K</i>, a target <i>Y</i> with &#8467; = cov(<i>x</i>, <i>Y</i>) and "
    "<i>v</i> = Var <i>Y</i>, and unknown means E<i>x</i> = <i>X</i>&beta;, E<i>Y</i> = <i>x</i><sub>0</sub><sup>T</sup>&beta;.",
    ["For which <i>d</i> is <i>d</i><sup>T</sup><i>x</i> unbiased for every &beta;?",
     "The best such <i>d</i> (Lagrange multipliers) and its error. Which part of the error is the price of estimating &beta;?",
     "Any other unbiased <i>d</i> loses exactly (<i>d</i> &minus; <i>d</i>*)<sup>T</sup><i>K</i>(<i>d</i> &minus; <i>d</i>*). "
     "When is the 2023 blend the best predictor?",
     "Next year's outcome instead of the level: why <i>z</i> stays the same."],
    "on the data, how much does the best predictor gain over the blend?",
    H("res:blup", "res:forecast"), "small to medium; the natural first chapter for E4&ndash;E7"))
s.append(ext(
    "E4. Monthly data and the season",
    "Monthly data have a season. The usual shortcut is to add up whole years and hope the season "
    "drops out. It does not when volumes are seasonal: a cohort sold mainly in summer leans on summer months.",
    "E&mu;<sub><i>jt</i></sub> = &beta;<sub><i>m</i>(<i>t</i>)</sub>, one unknown mean per calendar month "
    "(or per cohort and month), as fixed effects in E3; the target is the next 12 months.",
    ["The unbiasedness conditions: one per calendar month.",
     "When the predictor that ignores the season equals the seasonal one, and its bias otherwise. "
     "Try one cohort, two years of two months, twice the volume in the first month.",
     "With known covariances, aggregating to annual totals never helps. What can change once the "
     "season must be estimated?"],
    "does a monthly fit with an estimated season beat annual totals once everything is estimated?",
    H("res:blup", "res:season"), "medium"))
s.append(ext(
    "E5. A persistent common factor",
    "A pure period shock is gone the next month. Travel demand persists over months and years, and in "
    "the pandemic it broke. Then past months say something about future ones, through the factor.",
    "add a factor &lambda;<sub><i>i</i></sub>&lambda;<sub><i>j</i></sub>&Gamma;<sub><i>ts</i></sub> to E2, with "
    "loadings &lambda;<sub><i>j</i></sub> and a covariance &Gamma; over months, e.g. AR(1), "
    "&Gamma;<sub><i>ts</i></sub> = &gamma;&phi;<sup>|<i>t</i>&minus;<i>s</i>|</sup>, or a block &Gamma; with a break at known dates.",
    ["<i>K</i> and &#8467; for the next 12 months, and <i>K</i> &#8827; 0 for any observed cells.",
     "A small example where a best weight is negative although &phi; &gt; 0. Why is it not an error?",
     "Products of two cohorts' changes over 12 months, at lag &ge; 1: unbiased for the factor, and "
     "free of the shock and the season?",
     "Why loadings need three cohorts. When do relative prices between cohorts not depend on the factor?"],
    "are lagged products between cards different from zero? Does the factor model predict better than "
    "the shock model? Which treatment of the pandemic predicts the later years best?",
    H("res:factor", "res:factor_est", "res:factor_extra", "res:relativity_factor"), "large"))
s.append(ext(
    "E6. Frequency and severity",
    "A ratio is frequency times severity, and the two may need different credibility. The levels "
    "become vectors and <i>z</i> becomes a matrix.",
    "a level vector (frequency, severity) per cohort, a joint <i>K</i> over cohorts &times; components, "
    "and the frequency weighted by volume, the severity by claim counts.",
    ["The best credibility matrix <i>Z<sub>j</sub></i> (a matrix parabola).",
     "Joint and separate prediction coincide when the components do not covary. Is the converse true?",
     "The bias of the pure premium as a product of two predictions: E[<i>f&#770;s&#770;</i>] &minus; E[<i>fs</i>]."],
    "do frequency and severity residuals covary, and does a joint fit predict better?",
    H("res:vector", "res:freqsev_joint", "res:prodBias"), "medium"))
s.append(ext(
    "E7. A known demand index",
    "If a public series (passenger statistics) tracks demand, use it as a covariate with a "
    "cohort-specific sensitivity. This is Hachemeister's regression credibility, with demand in place of time.",
    "&mu;<sub><i>jt</i></sub> = &alpha;<sub><i>j</i></sub> + &beta;<sub><i>j</i></sub><i>D<sub>t</sub></i> + noise, "
    "(&alpha;<sub><i>j</i></sub>, &beta;<sub><i>j</i></sub>) random around a common mean, cohorts correlated as in E2.",
    ["Hachemeister's credibility matrix as an instance of E6's <i>Z<sub>j</sub></i>, with correlated cohorts.",
     "Equal sensitivities: when does the index act as a plain exposure adjustment?"],
    "given the index, how much correlation between cards remains?",
    H("res:vector"), "medium"))
s.append(ext(
    "E8. The price of estimation",
    "Formulas with known <i>K</i> are the oracle. In practice <i>K</i> is estimated from the same data, "
    "and claims are skewed. That can bias the premium and cost accuracy.",
    "any fit whose weights <i>d&#770;</i> are computed from the data, compared with the best weights <i>d</i>* "
    "for the true moments.",
    ["The error of the plug-in predictor is mse(<i>d</i>*) + E<i>B</i>&sup2; + 2E[<i>AB</i>], "
     "<i>A</i> the oracle's error and <i>B</i> the plug-in's distance from it. Under normal noise E[<i>AB</i>] = 0 "
     "(a distributional result; state the assumption).",
     f"The bias of estimated weights, &Sigma;<sub><i>i</i></sub> cov(<i>d&#770;<sub>i</sub></i>, {mu_hat}<sub><i>i</i></sub>): "
     "why it is negative for right-skewed claims, and why balancing the total premium removes it at portfolio level.",
     "An estimated table need not be positive definite. Projecting it onto valid tables never increases the error."],
    "how skewed are the residuals, and what does balancing the total premium cost in accuracy?",
    H("res:randomWeights", "res:plugIn", "res:valid_tables"), "medium"))
s.append(Spacer(1, 3))
s.append(Paragraph(
    "<i>Other directions in the handbook, not needed for the card data:</i> a known claim trend "
    f"({H('res:trend')}), a shared level within groups of cohorts ({H('res:phi', 'res:groups', 'res:twostage', 'res:est_groups')}), "
    f"when to merge cohorts and how to choose them ({H('res:merge', 'res:pool_intervals', 'res:blend_intervals')}), "
    f"and balance ({H('res:balance', 'res:bestBalanced', 'res:commonShift')}).", body))

# ---------------------------------------------------------------- 4. method
s.append(Paragraph("4. Comparing models on data (needed for every choice)", h))
s.append(Paragraph(
    "The theory says what is best <i>if</i> a model holds, not which model holds. Decide on the data "
    "by out-of-sample prediction. Use a rolling origin with no look-ahead: at each month, refit every "
    "alternative on the past only, predict each cohort's next 12 months, and score the squared error. "
    "Compare two alternatives by their <i>paired</i> loss differences, so the target year's common "
    "shock cancels. Test with Diebold&ndash;Mariano, a HAC variance with lag 11 and the "
    "Harvey&ndash;Leybourne&ndash;Newbold correction. Do not use shuffled K-fold: the common factor "
    "correlates held-out months with the training months.", body))
s.append(Spacer(1, 3))
s.append(Paragraph(
    "First check the power in simulation. In a world the size of the data, how often does the test "
    "find a real difference? (The app's first answer: with 6&ndash;8 years a 30% gap is found in only "
    "15&ndash;23% of draws.) \"No evidence of a difference\" is then a result in itself, and so is "
    "finding that a statement in the handbook is wrong or of little practical use.", body))

# ---------------------------------------------------------------- 5. the data
s.append(Paragraph("5. The application: travel insurance on payment cards", h))
s.append(Paragraph(
    "A travel insurance is sold through several card products. For each card product (a cohort) and "
    "month we have the cards in force, claim counts and paid amounts. The task is to price each card "
    "for the next underwriting year. Classical credibility treats the cards as independent, but travel "
    "demand moves them all at once, with the pandemic as the extreme case. On top of that the business "
    "is seasonal, volumes differ widely between cards, and cards start and stop within the window. The "
    "pricing questions map to the extensions:", body))
s.append(bullets([
    "Does the correlation between cards shrink with volume, or is it a common shock? (E2, E5)",
    "Does the common movement persist, do cards load on it equally, and does a public index capture it? (E5, E7)",
    "Monthly data with an estimated season, or annual totals? (E3, E4)",
    "Frequency and severity combined, separate or joint? (E6)",
    "How should new and closed cards enter the fit? (E1)",
]))
s.append(Spacer(1, 3))
s.append(Paragraph(
    "<i>Left to the student:</i> the number of factors, the treatment of the pandemic, reporting delay "
    "(simplest: use developed months only), and whether new cardholders behave differently. "
    "<i>Data and publication:</i> aggregated or anonymized company data by agreement, and the thesis "
    "text is public. The analysis must also run on simulated data (the app can produce it), so it can be "
    "reproduced without the company data.", body))

# ---------------------------------------------------------------- 6. how to work
s.append(Paragraph("6. How to work", h))
s.append(bullets([
    "<b>Derive first, then check.</b> For each extension, derive the listed results by hand. Then compare "
    "with the handbook, which gives the formula, a practical note and the proof idea. Where you disagree, "
    "find out who is right.",
    "<b>Guidance, not authority.</b> The continuation was developed with extensive AI assistance. Its "
    "proofs are machine-checked, so a stated result follows from its definitions. A machine cannot check "
    "whether the definitions say what is intended, whether a model fits real data, or whether a result "
    "is already known. Say so where a statement is wrong, known, or of little use.",
    "<b>No Lean needed.</b> Every handbook result links to its machine-checked proof in the proof "
    "assistant Lean (the blueprint). Reading it is optional.",
    "<b>Your own code</b> (R or Python) for estimation and back-testing. The app is for intuition and "
    "for checking the method, not a dependency.",
    "<b>Moments, not distributions.</b> The core model assumes first and second moments only. A "
    "distributional result (normal noise, gamma amounts) is fine if stated as such.",
    "<b>No hand-set tuning.</b> Every parameter of a fitted model is estimated from the data.",
]))

# ---------------------------------------------------------------- 7. sources
s.append(Paragraph("7. Where to find things", h))
s.append(table([
    ["<b>Where</b>", "<b>What you find there</b>"],
    ["<b>Handbook</b> (site, handbook.pdf)", "Each result with its formula, when to use it, what to watch out for, "
     "and why it holds. The numbers in this proposal refer to it."],
    ["<b>Paper</b> (site /paper/)", "The up-to-date version of the 2023 thesis: concepts and intuition, organized for lookup."],
    ["<b>App</b> (site /app/)", "Simulated worlds: draw data, fit models that never see the truth, compare with the "
     "best possible fit. \"Monthly cohorts\" is a world like the card data."],
    ["<b>FINDINGS.md</b>", "Gaps and surprises found so far, each with a counterexample or proof."],
    ["<b>studies/literature.md</b>", "Annotated literature: credibility, small-area estimation, covariance "
     "shrinkage; &sect;10 for monthly card data."],
    ["<b>Blueprint</b> (site, optional)", "Every statement with its full proof and a dependency graph."],
], [4.6*cm, 11.8*cm]))

# ---------------------------------------------------------------- 8. plan
s.append(Paragraph("8. Suggested phases", h))
s.append(bullets([
    "<b>Background.</b> Read the 2023 thesis (or the paper) and B&uuml;hlmann&ndash;Gisler ch. 4. "
    "Rederive section 2 above.",
    "<b>Choose</b> two or three extensions and derive their results, checking against the handbook.",
    "<b>Data.</b> Descriptive analysis: volumes, season, correlations between cards by lag, the pandemic.",
    "<b>Simulation check.</b> Does the comparison of section 4 have the power to separate your alternatives?",
    "<b>Comparison on data</b> and recommendations for pricing card products, with a list of "
    "statements checked, corrected or found already known.",
], numbered=True))

s.append(Paragraph("Prerequisites", h))
s.append(Paragraph("Linear models and mixed models (variance components), credibility theory, time series "
                   "basics, simulation, R or Python.", body))

s.append(Paragraph("Starting references", h))
s.append(bullets([
    THESIS, REPO, BG,
    "Goldberger, A. S. (1962). Best linear unbiased prediction in the generalized linear regression model. "
    "<i>JASA</i> 57, 369&ndash;375.",
    "Hachemeister, C. A. (1975). Credibility for regression models with application to trend. In "
    "<i>Credibility: Theory and Applications</i>, Academic Press.",
    "Frees, E. W. (2004). <i>Longitudinal and Panel Data</i>. Cambridge University Press.",
    "Rao, J. N. K. and Molina, I. (2015). <i>Small Area Estimation</i>, 2nd ed. Wiley.",
    "Diebold, F. X. and Mariano, R. S. (1995). Comparing predictive accuracy. <i>JBES</i> 13, 253&ndash;263.",
], style=ref))

doc.build(s)
print("ok")
