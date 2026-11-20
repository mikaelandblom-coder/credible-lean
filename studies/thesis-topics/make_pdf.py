"""Builds thesis_topics.pdf: a menu of three master thesis topics continuing
correlated credibility. Edit this script, not the PDF, and rerun it."""
from reportlab.lib.pagesizes import A4
from reportlab.platypus import (SimpleDocTemplate, Paragraph, Spacer, ListFlowable, ListItem,
                                PageBreak, Table, TableStyle)
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib.units import cm
from reportlab.lib import colors

out = "thesis_topics.pdf"
doc = SimpleDocTemplate(out, pagesize=A4, leftMargin=2.3*cm, rightMargin=2.3*cm,
                        topMargin=1.8*cm, bottomMargin=1.8*cm,
                        title="Master Thesis Topics: Correlated Credibility (draft v1)")
ss = getSampleStyleSheet()
title = ParagraphStyle("T", parent=ss["Title"], fontName="Helvetica-Bold", fontSize=18, leading=22, spaceAfter=2)
sub = ParagraphStyle("S", parent=ss["Normal"], fontName="Helvetica-Oblique", fontSize=10, textColor=colors.grey, alignment=1, spaceAfter=12)
h = ParagraphStyle("H", parent=ss["Heading2"], fontName="Helvetica-Bold", fontSize=12, spaceBefore=8, spaceAfter=3, textColor=colors.HexColor("#1f3a5f"))
body = ParagraphStyle("B", parent=ss["Normal"], fontName="Helvetica", fontSize=10, leading=13.6)
ref = ParagraphStyle("R", parent=body, fontSize=9.3, leading=12.2)
ttl = ParagraphStyle("TT", parent=body, fontName="Helvetica-Bold", fontSize=12, spaceAfter=2)
lvl = ParagraphStyle("L", parent=body, fontName="Helvetica-Oblique", fontSize=10, textColor=colors.grey, spaceAfter=6)
cell = ParagraphStyle("C", parent=body, fontSize=9.8, leading=13)


def bullets(items, numbered=False, style=body):
    return ListFlowable([ListItem(Paragraph(i, style), leftIndent=14) for i in items],
                        bulletType="1" if numbered else "bullet",
                        leftIndent=16, bulletFontSize=10)


THESIS = ("Andblom, M. (2023). <i>Generalized B&uuml;hlmann&ndash;Straub credibility theory for "
          "correlated data</i>. Master Thesis in Actuarial Mathematics 2023:2, Stockholm University.")
REPO = ("<i>credible-lean: a Lean 4 formalization of correlated credibility theory</i> (2026). "
        "doi:10.5281/zenodo.24054631. Includes a paper draft, a practitioner's handbook and a log of findings.")
BG = ("B&uuml;hlmann, H. and Gisler, A. (2005). <i>A Course in Credibility Theory and its Applications</i>. "
      "Springer (selected chapters).")

s = []

# ---------------------------------------------------------------- intro page
s.append(Paragraph("Master Thesis Topics", title))
s.append(Paragraph("Correlated credibility &middot; draft v1", sub))

s.append(Paragraph("Background", h))
s.append(Paragraph(
    "Classical B&uuml;hlmann&ndash;Straub credibility assumes that the estimates for different cohorts "
    "(risk groups, segments, years of entry) are independent. In practice a common shock, such as a change "
    "in travel demand or in the economy, moves several cohorts at once. A master thesis from Stockholm "
    "University (Andblom, 2023) generalized credibility to correlated cohorts. The work has since been "
    "continued: the results have been restated in a common framework, extended (unequal observation "
    "lengths, group structure, trends, common shocks, vector-valued levels) and several gaps and new results "
    "have been found.", body))

s.append(Paragraph("Why a review is needed", h))
s.append(Paragraph(
    "The continuation was developed with extensive use of AI assistance. Its mathematical statements are "
    "proved in the proof assistant Lean, so the proofs themselves are machine-checked. What a machine "
    "cannot check is whether the statements and definitions say what is intended, whether the models fit "
    "real insurance data, whether results presented as new are already known, and whether the simulation "
    "studies outside Lean are sound. Each topic below therefore combines an <b>independent review</b> of a "
    "group of results with an <b>open research question</b>. The student derives the reviewed results "
    "by hand, without relying on the existing code, and is free to conclude that a result is wrong, "
    "already known or of little practical use. Writing Lean is not required; reading the Lean "
    "statements is optional.", body))

s.append(Paragraph("Choosing a topic", h))
rows = [
    [Paragraph("<b>Topic</b>", cell), Paragraph("<b>Level</b>", cell), Paragraph("<b>Main skills</b>", cell)],
    [Paragraph("1. Correlated credibility against the best linear predictor", cell),
     Paragraph("Standard", cell), Paragraph("Linear algebra, simulation, R or Python", cell)],
    [Paragraph("2. Correlated credibility on public insurance data", cell),
     Paragraph("Standard to ambitious", cell), Paragraph("Data analysis, model checking, back-testing", cell)],
    [Paragraph("3. Group structure: correlated hierarchical credibility", cell),
     Paragraph("Ambitious", cell), Paragraph("Variance components, estimation theory, literature", cell)],
]
t = Table(rows, colWidths=[8.2*cm, 3.2*cm, 5.0*cm])
t.setStyle(TableStyle([
    ("LINEBELOW", (0, 0), (-1, 0), 0.6, colors.HexColor("#1f3a5f")),
    ("LINEBELOW", (0, 1), (-1, -1), 0.25, colors.lightgrey),
    ("VALIGN", (0, 0), (-1, -1), "TOP"),
    ("TOPPADDING", (0, 0), (-1, -1), 3), ("BOTTOMPADDING", (0, 0), (-1, -1), 4),
]))
s.append(t)
s.append(Spacer(1, 6))
s.append(Paragraph(
    "The topics are independent and can be adapted to the student's interests. Two students may take "
    "different topics in parallel. All topics use only simulated or public data, and the thesis will be public.",
    body))

s.append(Paragraph("Common starting references", h))
s.append(bullets([THESIS, REPO, BG], style=ref))

# ---------------------------------------------------------------- topic 1
s.append(PageBreak())
s.append(Paragraph("Topic 1. Correlated credibility against the best linear predictor", ttl))
s.append(Paragraph("Level: standard", lvl))

s.append(Paragraph("Background", h))
s.append(Paragraph(
    "The 2023 thesis estimates each cohort's level as a blend of its own estimate and a portfolio estimate, "
    "with an optimal credibility factor and optimal portfolio weights when the cohort estimates are "
    "correlated. The classical benchmark is wider: the best linear unbiased predictor, which may weight every "
    "cohort separately. Recent work states how much the blend loses against that predictor, when it loses "
    "nothing, and how much is lost by ignoring the correlation altogether (classical B&uuml;hlmann&ndash;Straub). "
    "All of these statements assume that the covariances are known.", body))

s.append(Paragraph("Research questions", h))
s.append(bullets([
    "<b>Review.</b> Are the stated results correct and correctly interpreted: the optimal credibility factor "
    "and weights, the loss of the blend against the best linear unbiased predictor, and the bounds on the "
    "cost of ignoring correlation? Are they already known in the credibility or econometrics literature?",
    "<b>Estimated parameters.</b> In practice the covariances are estimated from the same data. How much of "
    "the advantage of the correlated blend, or of the full predictor, survives estimation, and when is the "
    "simpler classical model the better choice?",
], numbered=True))

s.append(Paragraph("Requirements", h))
s.append(bullets([
    "The reviewed results are derived by hand in the thesis, independently of the existing code.",
    "Numerical claims are reproduced with the student's own code (R or Python).",
    "Recommendations should rest on explicit formulas where possible; simulation is used for evaluation.",
]))

s.append(Paragraph("Phases", h))
s.append(bullets([
    "<b>Review phase.</b> Literature review and derivation of the reviewed results; a short note on which "
    "hold, which need extra conditions and which are known.",
    "<b>Research phase.</b> Two to three candidate approaches to the estimation question, agreed with the supervisors.",
    "<b>Simulation study</b> with known true parameters, against the baselines: classical "
    "B&uuml;hlmann&ndash;Straub, and the correlated methods with the true parameters as an oracle.",
    "<b>Evaluation and recommendations.</b>",
], numbered=True))

s.append(Paragraph("Evaluation criteria", h))
s.append(Paragraph(
    "Agreement of the reviewed results with the student's derivations; mean squared error of prediction with "
    "estimated parameters; robustness to the number of cohorts, the number of periods and the size of the correlation.", body))

s.append(Paragraph("Prerequisites", h))
s.append(Paragraph("Linear algebra, linear models, basic credibility theory, simulation.", body))

s.append(Paragraph("Suggested starting references", h))
s.append(bullets([
    "Thesis, repository and B&uuml;hlmann &amp; Gisler as on the first page.",
    "Goldberger, A. S. (1962). Best linear unbiased prediction in the generalized linear regression model. "
    "<i>Journal of the American Statistical Association</i> 57, 369&ndash;375.",
    "Prasad, N. G. N. and Rao, J. N. K. (1990). The estimation of the mean squared error of small-area "
    "estimators. <i>Journal of the American Statistical Association</i> 85, 163&ndash;171.",
    "Yeo, K. L. and Valdez, E. A. (2006). Claim dependence with common effects in credibility models. "
    "<i>Insurance: Mathematics and Economics</i> 38(3).",
], style=ref))

# ---------------------------------------------------------------- topic 2
s.append(PageBreak())
s.append(Paragraph("Topic 2. Correlated credibility on public insurance data", ttl))
s.append(Paragraph("Level: standard to ambitious", lvl))

s.append(Paragraph("Background", h))
s.append(Paragraph(
    "The correlated credibility results are proved under assumptions on first and second moments only. "
    "Whether these assumptions describe real portfolios has not been tested. Recent work suggests that the "
    "thesis model, in which the correlation between cohorts is fixed while variances fall with volume, may "
    "misdescribe a common shock, whose effect does not shrink with volume; an alternative model with a common "
    "shock plus process noise has been proposed. Trends over time raise similar questions.", body))

s.append(Paragraph("Research questions", h))
s.append(bullets([
    "<b>Review.</b> Are the modelling assumptions and the proposed alternatives (common shock, trends) "
    "correctly derived, and are their parameter estimators unbiased as claimed?",
    "<b>Evidence.</b> Is there correlation between cohorts in public insurance data, and which covariance model "
    "describes it best?",
    "<b>Prediction.</b> Does correlated credibility predict better out of sample than classical "
    "B&uuml;hlmann&ndash;Straub, and under which portfolio characteristics?",
], numbered=True))

s.append(Paragraph("Requirements", h))
s.append(bullets([
    "Only public data, for example the CAS loss reserving database (NAIC Schedule P) or the classical "
    "Hachemeister data. No proprietary data.",
    "Model choice and evaluation are based on out-of-sample prediction, with the evaluation design fixed "
    "before results are compared.",
    "Fitted models have no hand-set tuning parameters.",
]))

s.append(Paragraph("Phases", h))
s.append(bullets([
    "<b>Review phase.</b> Derivation of the reviewed models and estimators; literature review.",
    "<b>Data phase.</b> Choice of data sets, definition of cohorts and periods, descriptive analysis.",
    "<b>Fitting and back-testing</b> of the candidate models against classical B&uuml;hlmann&ndash;Straub, "
    "complemented by a simulation study where the true model is known.",
    "<b>Evaluation and recommendations,</b> including a short practitioner summary.",
], numbered=True))

s.append(Paragraph("Evaluation criteria", h))
s.append(Paragraph(
    "Out-of-sample prediction error, stability of the estimated parameters, diagnostic fit of the covariance "
    "models, and clarity of guidance on when correlation should be modelled.", body))

s.append(Paragraph("Prerequisites", h))
s.append(Paragraph("Basic non-life insurance mathematics, credibility theory, statistical inference, R or Python.", body))

s.append(Paragraph("Suggested starting references", h))
s.append(bullets([
    "Thesis, repository and B&uuml;hlmann &amp; Gisler as on the first page.",
    "Meyers, G. and Shi, P. (2011). Loss reserving data pulled from NAIC Schedule P. Casualty Actuarial Society.",
    "Hachemeister, C. A. (1975). Credibility for regression models with application to trend. In Kahn, P. M. (ed.), "
    "<i>Credibility: Theory and Applications</i>. Academic Press. Data in the R package <i>actuar</i> "
    "(Dutang, Goulet and Pigeon, 2008, <i>Journal of Statistical Software</i> 25(7)).",
    "Frees, E. W., Young, V. R. and Luo, Y. (1999). A longitudinal data analysis interpretation of "
    "credibility models. <i>Insurance: Mathematics and Economics</i> 24, 229&ndash;247.",
], style=ref))

# ---------------------------------------------------------------- topic 3
s.append(PageBreak())
s.append(Paragraph("Topic 3. Group structure: correlated hierarchical credibility", ttl))
s.append(Paragraph("Level: ambitious", lvl))

s.append(Paragraph("Background", h))
s.append(Paragraph(
    "Cohorts often fall into groups, for example products within a line of business, so that cohorts in the "
    "same group share part of their level. Hierarchical credibility (Jewell, Taylor) and nested error models in "
    "small-area estimation handle this when the estimates are independent. The correlated framework has been "
    "extended to group levels, with correlated noise. One finding is that the thesis estimator of the level "
    "variance becomes biased when cohorts share a group level, and that pairs of cohorts within and across "
    "groups identify the shared part.", body))

s.append(Paragraph("Research questions", h))
s.append(bullets([
    "<b>Review.</b> Are the group extension, its optimal weights and the bias result correctly derived? How do "
    "they relate to classical hierarchical credibility and to nested error models: what is new and what is known?",
    "<b>Estimation.</b> How should the variance components of a group structure with correlated cohorts be "
    "estimated in practice, and how does the choice affect the prediction error?",
    "<b>Structure.</b> When does modelling the group structure pay off compared with ignoring it or treating "
    "the groups as separate portfolios?",
], numbered=True))

s.append(Paragraph("Requirements", h))
s.append(bullets([
    "The reviewed results are derived by hand in the thesis, independently of the existing code.",
    "Estimators should be explicit and implementable without resampling; simulation is used for evaluation.",
    "Fitted models have no hand-set tuning parameters. Only simulated or public data.",
]))

s.append(Paragraph("Phases", h))
s.append(bullets([
    "<b>Review phase.</b> Literature review (hierarchical credibility, small-area estimation, variance "
    "component estimation) and derivation of the reviewed results.",
    "<b>Research phase.</b> Two to three candidate estimation approaches, agreed with the supervisors.",
    "<b>Simulation study</b> against baselines: classical hierarchical credibility, the correlated model "
    "without groups, and the group model with true parameters as an oracle.",
    "<b>Evaluation and recommendations.</b>",
], numbered=True))

s.append(Paragraph("Evaluation criteria", h))
s.append(Paragraph(
    "Correctness of the reviewed results; bias and variance of the estimated components; mean squared error "
    "of prediction across numbers of groups, group sizes and correlation levels.", body))

s.append(Paragraph("Prerequisites", h))
s.append(Paragraph("Linear models, mixed models or variance components, credibility theory, simulation.", body))

s.append(Paragraph("Suggested starting references", h))
s.append(bullets([
    "Thesis, repository and B&uuml;hlmann &amp; Gisler (chapter 6) as on the first page.",
    "Jewell, W. S. (1975). The use of collateral data in credibility theory: a hierarchical model. "
    "IIASA Research Memorandum RM-75-24.",
    "Taylor, G. C. (1979). Credibility analysis of a general hierarchical model. "
    "<i>Scandinavian Actuarial Journal</i> 1979(1), 1&ndash;12.",
    "Stukel, D. M. and Rao, J. N. K. (1999). On small-area estimation under two-fold nested error regression "
    "models. <i>Journal of Statistical Planning and Inference</i> 78, 131&ndash;147.",
    "Rao, J. N. K. and Molina, I. (2015). <i>Small Area Estimation</i>, 2nd ed. Wiley.",
], style=ref))

doc.build(s)
print("ok")
