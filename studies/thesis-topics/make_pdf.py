"""Builds thesis_topics.pdf: the master thesis proposal "Correlation structure of claims across
card products" (notes/card-data.md, Step 8). It is the thesis worker's main document.
Edit this script, not the PDF, and rerun it: python3 make_pdf.py (needs reportlab)."""
from reportlab.lib.pagesizes import A4
from reportlab.platypus import (SimpleDocTemplate, Paragraph, Spacer, ListFlowable, ListItem,
                                Table, TableStyle, KeepTogether)
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib.units import cm
from reportlab.lib import colors

out = "thesis_topics.pdf"
doc = SimpleDocTemplate(out, pagesize=A4, leftMargin=2.3*cm, rightMargin=2.3*cm,
                        topMargin=1.8*cm, bottomMargin=1.8*cm,
                        title="Master Thesis Proposal: Correlation Structure of Claims across Card Products (draft v2)")
ss = getSampleStyleSheet()
NAVY = colors.HexColor("#1f3a5f")
title = ParagraphStyle("T", parent=ss["Title"], fontName="Helvetica-Bold", fontSize=17, leading=21, spaceAfter=2)
sub = ParagraphStyle("S", parent=ss["Normal"], fontName="Helvetica-Oblique", fontSize=10, textColor=colors.grey, alignment=1, spaceAfter=12)
h = ParagraphStyle("H", parent=ss["Heading2"], fontName="Helvetica-Bold", fontSize=12, spaceBefore=9, spaceAfter=3, textColor=NAVY)
h3 = ParagraphStyle("H3", parent=ss["Normal"], fontName="Helvetica-Bold", fontSize=10.3, spaceBefore=6, spaceAfter=2)
body = ParagraphStyle("B", parent=ss["Normal"], fontName="Helvetica", fontSize=10, leading=13.6)
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
REPO = ("<i>credible-lean: a Lean 4 formalization of correlated credibility theory</i> (2026). "
        "doi:10.5281/zenodo.24054631. Site: " + SITE + " (paper, handbook, app, blueprint).")
BG = ("B&uuml;hlmann, H. and Gisler, A. (2005). <i>A Course in Credibility Theory and its Applications</i>. "
      "Springer (chapters 4, 8 and 9).")

s = []

# ---------------------------------------------------------------- 1. overview
s.append(Paragraph("Correlation Structure of Claims across Card Products", title))
s.append(Paragraph("Master thesis proposal &middot; actuarial mathematics &middot; draft v2", sub))

s.append(Paragraph("1. The problem", h))
s.append(Paragraph(
    "A travel insurance product is sold through several payment cards. For each card product and month "
    "we have the cards in force, the claim counts and the paid amounts. The task is to price each card for "
    "the <b>next underwriting year</b>, i.e. to predict its claim cost over the next 12 months, using its own "
    "history and that of the other cards. Classical B&uuml;hlmann&ndash;Straub credibility assumes the cards' "
    "experience is independent. It is not: travel demand moves all cards at once, strongly from year to "
    "year, with the pandemic as the extreme case. On top of that the business is seasonal, volumes differ "
    "widely between cards, and cards start and stop within the observation window.", body))
s.append(Spacer(1, 4))
s.append(Paragraph(
    "A master thesis (Andblom, 2023) generalized credibility to correlated cohorts. The work has since "
    "been continued in a repository (credible-lean) that builds the theory for <b>a menu of models</b> "
    "for exactly this kind of data. For each model it states the best predictor, its error, and unbiased "
    "estimators of the parameters. What the theory cannot say is <b>which model holds for the real "
    "data</b>. That is the thesis: choose among the alternatives on actual card data, by out-of-sample "
    "prediction, and report what the data say about the correlation structure.", body))

s.append(Paragraph("2. Research questions", h))
s.append(bullets([
    "<b>Q1. Form of the correlation.</b> Does the correlation between cards shrink with volume (the 2023 "
    "thesis), or is it a common shock that does not (a period shock plus process noise)?",
    "<b>Q2. Persistence.</b> Is there a common demand factor that persists over months and years (AR(1), "
    "a break at known dates), and do cards load on it equally?",
    "<b>Q3. Seasonality.</b> Should the data be aggregated to years, or modelled per month with an "
    "<i>estimated</i> season?",
    "<b>Q4. Frequency and severity.</b> Model them combined (burning cost), separately, or jointly?",
    "<b>Q5. Entry and exit.</b> How should new and decommissioned cards enter the fit?",
]))
s.append(Spacer(1, 3))
s.append(Paragraph(
    "The answers need not be a single winning model. A well-supported \"no evidence of a difference\" "
    "between two alternatives is a result, and so is a finding that a theoretical statement in the "
    "repository is wrong or impractical.", body))

s.append(Paragraph("3. The starting point: every alternative is a switch", h))
s.append(Paragraph(
    "In the repository each modelling choice is a switch with proved consequences. (The Lean files call "
    "a card product a <i>cohort</i>; nothing there is specific to cards.) Names below are Lean "
    "declarations, which can be looked up in the blueprint.", body))
s.append(Spacer(1, 4))
s.append(table([
    ["<b>Switch</b>", "<b>Alternatives</b>", "<b>Where in the repo</b>"],
    ["Correlation form", "thesis <i>&sigma;&sigma;&rho;</i>; shock + process noise; common factor",
     code("Unequal", "Shock", "Factor") + " (" + code("Factor.K_posDef") + ")"],
    ["Factor over time", "independent months; AR(1); break at known dates; general &Gamma;; per-card dynamics",
     code("Factor.ar1_posSemidef", "Factor.regime_posSemidef", "Factor.KG_posDef")],
    ["Demand signal", "known index <i>D<sub>t</sub></i> with card-specific sensitivities; equal sensitivity "
     "(an exposure adjustment)", code("CoreVector.hachemeister_bestZ", "CoreVector.blupW_optimal_dotProduct")],
    ["Season", "none; known index; estimated fixed effects", code("Season.blup_eq_iff", "Unequal.a_eq_of_volume")],
    ["Aggregation", "monthly; annual totals", code("Core.predMse_aggregate_eq_blup_add")],
    ["Predictor", "thesis blend <i>z&mu;&#770;<sub>j</sub> + (1&minus;z)&mu;&#770;</i>; full best linear "
     "unbiased predictor", code("Core.blup_optimal", "Core.predMse_blup")],
    ["Frequency &times; severity", "combined; separate; joint (vector)",
     code("CoreVector.blupW_eq_sepW_of_componentBlockDiag")],
    ["Card set", "balanced; entry and exit (observed cells only)", "built into " + code("Factor") + " (any observed cells)"],
], [3.3*cm, 6.6*cm, 6.5*cm]))
s.append(Spacer(1, 4))
s.append(Paragraph(
    "The predictor for the 12-month target is the best linear unbiased predictor with fixed effects "
    "(Goldberger 1962, Harville 1976; universal kriging), proved once for any covariance table, target "
    "and design (" + code("Core.blup_optimal") + "). Its error splits into the error with known means plus "
    "the price of estimating them. Each model only supplies its covariance table.", body))

# ---------------------------------------------------------------- 4. extensions
s.append(Paragraph("4. Suggested extensions to explore on the data", h))
s.append(Paragraph(
    "Ordered roughly by how promising they look. Each item says what the theory predicts and what the data "
    "should be asked. The student picks a subset with the supervisors; the first three form a complete thesis "
    "on their own.", body))

ext = [
    ("A. Shock or factor? (Q1, Q2)",
     "A pure period shock is independent between months; a demand factor persists. Lagged cross-card "
     "products (different cards, lag &ge; 1 month) see only the factor, so they separate it from the shock. "
     "A shock-only fit on data with a persistent factor absorbs only part of it (Finding 26). With an AR(1) "
     "factor the best weights can be <i>negative</i> even with positive autocorrelation (Finding 25). "
     "<b>Data question:</b> are the lagged cross-card moments distinguishable from zero, and does the factor "
     "model predict better than the shock model?",
     code("Factor.yoy_unbiased_factor", "Factor.crossHat_ar1_two", "Factor.ar1_identified",
          "Factor.blup_neg_of_ar1")),
    ("B. Estimated season or annual totals? (Q3)",
     "Whole years do <i>not</i> make the season drop out when volumes are seasonal: the one-mean predictor "
     "leans on busy months and is biased (Finding 24). Annual aggregation is a restricted predictor and "
     "never better with known parameters, but the season must then be estimated. "
     "<b>Data question:</b> does the monthly fit with an estimated season beat annual totals once all "
     "parameters are estimated?",
     code("Season.blup_eq_iff", "Core.Target.integral_bias", "Core.predMse_blup_le_aggregate")),
    ("C. Choosing between fits on data (method for all items)",
     "Rolling origin with no look-ahead: at each month refit every alternative on the past only, predict "
     "each card's next 12 months, and score the squared error. Compare alternatives by <i>paired</i> loss "
     "differences (the target year's shock cancels), with a Diebold&ndash;Mariano test, HAC lag 11 and the "
     "Harvey&ndash;Leybourne&ndash;Newbold correction. Not shuffled K-fold: the common factor makes held-out "
     "months correlated with the training months. Built in the app (\u201cComparing fits on data\u201d). "
     "<b>Also:</b> use the app's simulated world, where the true error is known, to measure how often this "
     "comparison picks the better fit at the real sample size. First result: with 6&ndash;8 years the test "
     "finds a 30% gap in only 15&ndash;23% of draws, and rejects in 16&ndash;25% when two fits are equally good.",
     "notes/card-data.md Step 7b, studies/literature.md &sect;10i"),
    ("D. Equal or card-specific loadings (Q2)",
     "Loadings are identified only with three or more cards; two cards give the product only. Proved: "
     "any statistic picks up exactly g'&Gamma;g from the factor, g the loading-weighted month profile; "
     "card <i>relativities</i> are factor-free with equal loadings <i>and</i> the same month weights, but "
     "not with the same months alone (Finding 31: different volume patterns or a mid-window entry leave "
     "&gamma;(1&minus;&phi;)/2 in a two-month example). <b>Data question:</b> do the fitted loadings differ, "
     "and does it matter for ranking cards and for prediction?",
     code("Factor.load_sq_of_three", "Factor.quadTab_eq", "Factor.relCoef_factor_free", "Factor.extra_profile")),
    ("E. A public demand index (Q2)",
     "Official passenger statistics as a known covariate with card-specific sensitivities is Hachemeister's "
     "regression credibility with demand in place of time. <b>Data question:</b> conditional on the index, "
     "how much cross-card correlation remains? A signal never captures the whole shock, so the index and "
     "a latent factor can be combined.",
     code("CoreVector.hachemeister_bestZ", "CoreVector.blupW_optimal_dotProduct")),
    ("F. Frequency and severity (Q4)",
     "With a factor table per component (frequency weighted by cards, severity by claim counts), separate "
     "and joint prediction coincide when the components do not cross-correlate. The converse fails "
     "(Finding 32): with the same card structure in both, cross-correlation carries no information. So "
     "measure the gain of the joint fit rather than infer it from residual correlation. <b>Data question:</b> "
     "do frequency and severity residuals cross-correlate, and does the joint fit predict better?",
     code("FreqSev.blupW_eq_separate", "CoreVector.blupW_kronecker")),
    ("G. Estimation in practice",
     "Unbiased moment estimators exist given the factor's shape (Henderson III / MINQUE), but with traps: "
     "the process noise needs volume variation; card-specific means hide the common level &tau;&sup2; "
     "(Finding 27); under a card season one year identifies nothing and two years need seasonal volumes "
     "(Findings 28&ndash;29). Fitted tables may not be positive definite; projecting onto valid tables never "
     "increases the error, and gives a positive definite K&#770; when every noise estimate is positive "
     "(Finding 30). The AR(1) parameter is noisy with few years. <b>Data question:</b> how stable are the "
     "estimates, and is profiling &phi; good enough?",
     code("Factor.minque_ar1_two_years_unbiased", "Shock.not_unbiased_s2_of_const",
          "Factor.hendersonMat_cohortSeason_det_eq_zero", "ConeProjection.hsq_proj_add_le",
          "Factor.tableK_posDef")),
    ("H. The pandemic, entry and exit (Q5)",
     "The pandemic as a break at known dates (a block &Gamma;), an exclusion, or a large draw of the "
     "factor. Exited cards keep their past cells in the fit; the exact results assume the exit date is "
     "independent of the claims, so exits driven by results (Frees 2004) make them approximate. "
     "<b>Data question:</b> which treatment of the pandemic predicts the post-pandemic years best?",
     code("Factor.regime_posSemidef")),
]
for name, text, where in ext:
    s.append(KeepTogether([Paragraph(name, h3), Paragraph(text, body),
                           Paragraph("<i>In the repo:</i> " + where, lean)]))

# ---------------------------------------------------------------- 5. how to work
s.append(Paragraph("5. How to work with the repository", h))
s.append(Paragraph(
    "The continuation was developed with extensive AI assistance. Its proofs are machine-checked in "
    "the proof assistant Lean, so a proved statement follows from its definitions. A machine cannot "
    "check whether the definitions say what is intended, whether the models fit real data, whether a "
    "result presented as new is already known, or whether the simulation code is sound. Therefore:", body))
s.append(bullets([
    "Treat the repository as <b>guidance, not authority</b>. Derive by hand every result the thesis relies on, "
    "and say so where a statement is wrong, already known, or of little practical use.",
    "Write your own estimation and back-testing code (R or Python); the app is for intuition and for "
    "checking the protocol, not a dependency.",
    "Writing Lean is not required; reading the statements is optional, via the blueprint.",
    "The core model is distribution-free (first and second moments only). Distributional choices "
    "(Poisson counts, gamma amounts) are allowed in the simulation and stated as such.",
    "Fitted models have no hand-set tuning parameters: everything is estimated from the data.",
]))

# ---------------------------------------------------------------- 6. sources of inspiration
s.append(Paragraph("6. Sources of inspiration in the repository", h))
s.append(Paragraph(
    "Beyond the results cited above, the repository holds material worth reading early. It is a "
    "starting point; much of it was written for the author's own planning.", body))
s.append(Spacer(1, 4))
s.append(table([
    ["<b>Where</b>", "<b>What you find there</b>"],
    ["<b>Paper</b> (site /paper/)", "The up-to-date thesis: concepts and intuition, organized for lookup, with Lean names."],
    ["<b>Handbook</b> (site, handbook.pdf)", "Formulas with practical notes: when to use them, what to watch out for."],
    ["<b>App</b> (site /app/)", "Simulated worlds: draw data, fit models that never see the truth, compare with the oracle. "
     "Its \"Monthly cohorts\" section is a world like the card data (season, AR(1) factor, shock, seasonal volumes)."],
    ["<b>FINDINGS.md</b>", "Gaps and surprises found along the way, each with a counterexample or proof. "
     "Findings 22&ndash;30 concern this data directly."],
    ["<b>studies/literature.md</b>", "Annotated literature: credibility, small-area estimation (EBLUP), "
     "covariance shrinkage; &sect;10 is the literature for this thesis (seasonal and evolutionary "
     "credibility, factor models, panels with entry and exit, comparing forecasts)."],
    ["<b>notes/card-data.md</b>", "The plan behind this proposal: the switches, what was proved, what is open."],
    ["<b>notes/time-trends.md</b>, <b>notes/unequal-lengths.md</b>", "Trends and cards observed over different periods."],
    ["<b>studies/</b> scripts and PLAN.md", "Small simulation studies (e.g. MSEP with estimated parameters, "
     "damping the correlations, choosing shrinkage) with their outputs, and the plan for the app."],
    ["<b>Blueprint</b> (site)", "Every statement with its proof and a dependency graph; reached by link."],
], [4.6*cm, 11.8*cm]))

# ---------------------------------------------------------------- 7. plan
s.append(Paragraph("7. Suggested phases", h))
s.append(bullets([
    "<b>Literature and review.</b> Credibility with common effects, seasonal and evolutionary credibility, "
    "BLUP with fixed effects, variance components; derive the results the thesis will use.",
    "<b>Data.</b> Descriptive analysis: volumes, season, cross-card correlations by lag, the pandemic.",
    "<b>Simulation check.</b> In a simulated world sized like the data: does the rolling-origin comparison "
    "have the power to tell the alternatives apart?",
    "<b>Comparison on data.</b> Extensions A&ndash;C first, then a selection of D&ndash;H.",
    "<b>Recommendations</b> for pricing card products, and a list of statements checked, corrected or found known.",
], numbered=True))

s.append(Paragraph("Left to the student", h))
s.append(Paragraph(
    "The number of factors; whether loadings are equal; the treatment of the pandemic; reporting delay "
    "(simplest: use developed months only); whether new cardholders behave differently.", body))

s.append(Paragraph("Data and publication", h))
s.append(Paragraph(
    "Aggregated or anonymized company data by agreement; the thesis text is public. The method must also "
    "run on the app's simulated data, so the analysis can be reproduced without the company data.", body))

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
