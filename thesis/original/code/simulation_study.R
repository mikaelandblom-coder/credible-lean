library(randcorr)
library(tidyverse)
library(MASS)
library(scales)
library(clusterGeneration)
library(xtable)

set.seed(1549)

n_sims <- 10000

# Set fixed model parameters
tau     <- 0.6
mu      <- 1
n_terms <- 10
n_risks <- 9

# -- Comment out this part to get random corr matricss
# Generate biased correlation matrices
# rho_all <- array(NA, dim = c(n_risks, n_risks, n_sims*20))
# avg_rho <- array(NA, dim = n_sims)
# for(i in 1:(n_sims*3)){
#   #x <- genPositiveDefMat(n_risks, covMethod = "c-vine", rangeVar = c(1,1), eta = 0.01)
#   #rho_m <- x$Sigma
#   rho_m <- randcorr(n_risks)
#   rho_all[,,i] <- rho_m
#   avg_rho[i] <- mean(rho_m[lower.tri(rho_m)])
# }
# rho_filter <- order(avg_rho, decreasing = TRUE)[1:n_sims]
# rho_subset <- rho_all[,,rho_filter]

# -- Comment out this part to get all possible rho values
rho_sim <- seq(from = 1/(1-n_risks), to = 1, length.out = n_sims)
rho_subset <- array(NA, dim = c(n_risks, n_risks, n_sims))
avg_rho <- array(NA, dim = n_sims)
for(i in 1:n_sims){
  rho_subset[,,i] <- rho_sim[i]
  diag(rho_subset[,,i]) <- 1
  avg_rho[i] <- rho_sim[i]
}
rho_filter <- 1:n_sims

errors <- matrix(nrow = 2*n_sims, ncol = 7)
for (ind in n_sims:1) {
  
  # Generate random parameters
  mu_j  <- rgamma(n_risks, shape = mu^2/tau^2, rate = mu/tau^2)
  #mu_j <- rnorm(n_risks, mean = mu, sd = tau)
  #sigma <- sqrt(rnorm(n_risks, 20e6, 5e6))
  sigma <- sqrt(rlnorm(n_risks, 16, sqrt(2))) # exp(16 + sqrt(2)/2) = 24.2m, (exp(2)-1)*(exp(2*16 + 2))
  #sigma <- pmin(sigma, sqrt(30e6))
  #sigma <- sqrt(rnorm(n_risks, mean = 24e6, sd = 5e6))
  w_j   <- rnorm(n_risks, 3e6, 300e3)
  w     <- t(sapply(1:n_risks, function(x) rnorm(n_terms, w_j[x], w_j[x]/10)))
  rho   <- rho_subset[,,ind]
  
  # Calculate weights a
  a <- w / rowSums(w)
  
  # Generate data
  eps_jt <- t(mvrnorm(n = n_terms, mu = rep(0, n_risks), Sigma = rho))
  mu_jt <- mu_j + sigma/sqrt(w) * eps_jt
  
  # Risk specific estimate
  mu_j_hat <- rowSums(a * mu_jt)
  
  # Estimate correlation matrix
  sigma_rho <- matrix(nrow = n_risks, ncol = n_risks)
  for(i in 1:n_risks){
    for(j in 1:n_risks){
      sigma_rho[i,j] <- sum(sqrt(w[i,]*w[j,])*(mu_jt[i,]-mu_j_hat[i])*(mu_jt[j,]-mu_j_hat[j]))/(sum(sqrt(w[i,]*w[j,]))+(n_terms-2)*sum(w[i,])*sum(w[j,])/sum(sqrt(w[i,]*w[j,])))
    }
  }
  
  # Estimate correction term
  cj <- matrix(nrow = n_risks, ncol = 1)
  for(j in 1:n_risks){
    tmp <- matrix(nrow = n_risks, ncol = 1)
    for(i in 1:n_risks){
      tmp[i] <- ((i==j)-sum(w[i,])/sum(w))*sigma_rho[i,j]
    }
    cj[j] <- sum(tmp)
  }
  
  # Crude estimate for mu
  avg_mu_hat <- sum(rowSums(w) * mu_j_hat)/sum(w)
  
  # Estimate tau
  tau_j <- matrix(nrow = n_risks, ncol = 1)
  for(j in 1:n_risks){
    tau_j[j] <- sum(w[j,]) * ((mu_j_hat[j] - avg_mu_hat)^2 - cj[j])
  }
  tau_est <- sum(tau_j) / (sum(w)-sum(rowSums(w)^2)/sum(w))
  #tau_est <- max(tau_est, 0)
  
  # Estimate covariance matrix
  K_bar <- sigma_rho + diag(tau_est, nrow = n_risks, ncol = n_risks)
  K_bar_inv <- solve(K_bar)
  
  # Model parameters
  s2 <- 1/sum(K_bar_inv)
  b  <- rowSums(K_bar_inv) * s2
  
  ##b <- (b - min(b))/(max(b)-min(b))
  #b <- pmin(pmax(b, 0), 1)
  #b <- b/sum(b)

  # Calculate blended premium
  mu_hat <- c(b %*% mu_j_hat)
  z <- (1-b)*tau_est/(tau_est + diag(sigma_rho) - s2)
  #z <- pmin(pmax(z, 0), 1)
  blended <- mu_j_hat * z +  mu_hat * (1-z)
  
  # Calculate total costs
  tot_cost <- sum(w*mu_jt)
  tot_cost_est <- sum(w*blended)
  
  # ------- Buhlmann
  sig_j <- rowSums(w*(mu_jt - mu_j_hat)^2)/(n_terms-1)  
  sig   <- mean(sig_j)
  tau_b <- (sum(rowSums(w)*(mu_j_hat - avg_mu_hat)^2) - (n_risks-1)*sig)/(sum(w) - sum(rowSums(w)^2)/sum(w))
  #tau_b <- max(tau_b, 0)
  z_b   <- rowSums(w)/(rowSums(w) + sig/tau_b)
  mu_b  <- c(z_b %*% mu_j_hat)/sum(z_b)
  mu_b  <- ifelse(is.na(mu_b), tot_cost/sum(w), mu_b)
  blended_b <- mu_j_hat * z_b + mu_b * (1-z_b)
  tot_cost_b <- sum(w*blended_b)
  
  
  errors[2*ind - 1,] <- c(ind,
                          (tau_est - tau^2)/tau^2,
                          mean((blended-mu_j)/mu_j),
                          #sum(rowSums(w)*(blended-mu_j)/mu_j)/sum(w),
                          (mu_hat - mu)/mu,
                          (tot_cost_est - tot_cost)/tot_cost,
                          "Proposed",
                          avg_rho[rho_filter][ind])
  
  errors[2*ind,] <- c(ind,
                      (tau_b - tau^2)/tau^2,
                      mean((blended_b-mu_j)/mu_j),
                      #sum(rowSums(w)*(blended_b-mu_j)/mu_j)/sum(w),
                      (mu_b - mu)/mu,
                      (tot_cost_b - tot_cost)/tot_cost,
                      "Bühlmann-Straub",
                      avg_rho[rho_filter][ind])
  }

dummy <- as_tibble(errors) %>%
  setNames(., c("index", "tau", "mu_j", "mu", "balance", "model", "rho")) %>%
  mutate(across(-model, ~as.numeric(.x))) %>%
  pivot_longer(!c(index, model, rho), names_to = "error_type", values_to = "rel_error") %>%
  add_row(tibble(index = 1:n_sims,
                 model = "stat",
                 error_type = "rho",
                 rho = avg_rho[rho_filter],
                 rel_error = rho)) %>%
  group_by(model, error_type) %>%
  mutate(avg = mean(rel_error)) %>%
  ungroup()

# ggplot(dummy, aes(x = model, y = rel_error)) +
#   geom_boxplot() +
#   facet_wrap(~error_type, scales = "free")

# ggplot(dummy %>% filter(error_type == "tau"), aes(x = rel_error, fill = model)) +
#   geom_density(alpha=.3) +
#   scale_x_continuous(trans = "pseudo_log")

# ggplot(dummy, aes(x = rel_error, fill = model)) +
#  facet_wrap(~error_type, scales = "free") +
#  geom_density(alpha=.5) +
#  #geom_histogram(position = "identity") +
#  scale_x_continuous(trans = "pseudo_log")
#  #coord_cartesian(xlim = c(-0.1, 0.1))
#  #xlim(c(-0.1, 0.1))


# ---------------- Plot it individually

ggplot(dummy %>% filter(error_type == "mu"), aes(x = rel_error, fill = model)) +
  geom_density(alpha=.5) +
  scale_x_continuous(trans = "pseudo_log", breaks = c(-1, -0.5, -0.25, 0, 0.25, 0.5, 1), labels = percent) +
  coord_cartesian(xlim = c(-1, 1)) +
  #coord_cartesian(xlim = c(-2, 2)) +
  #scale_x_continuous(labels = percent) +
  labs(x = expression(paste("relative estimation error in ", mu)),  fill = "Model", color = "Model") +
  theme_bw() +
  geom_vline(data = dummy %>% filter(error_type == "mu"), aes(xintercept = avg, color = model), size = 1) +
  theme(text = element_text(size = 20))

ggplot(dummy %>% filter(error_type == "mu_j"), aes(x = rel_error, fill = model)) +
  geom_density(alpha=.5) +
  scale_x_continuous(trans = "pseudo_log", breaks = c(-1.5, -1, -0.5, -0.25, 0, 0.25, 0.5, 1, 1.5), labels = percent) +
  coord_cartesian(xlim = c(-1, 1.5)) +
  #scale_x_continuous(labels = percent) +
  labs(x = expression(paste("relative estimation error in ", mu[j])),  fill = "Model", color = "Model") +
  theme_bw() +
  geom_vline(data = dummy %>% filter(error_type == "mu_j"), aes(xintercept = avg, color = model), size = 1) +
  theme(text = element_text(size = 20))

ggplot(dummy %>% filter(error_type == "tau"), aes(x = rel_error, fill = model)) +
  geom_density(alpha=.5) +
  scale_x_continuous(trans = "pseudo_log", breaks = c(-1, -0.5, -0.25, 0, 0.25, 0.5, 1, 1.5) , labels = percent) +
  coord_cartesian(xlim = c(-1, 1.5)) +
  #coord_cartesian(xlim = c(-1, 2)) +
  #scale_x_continuous(labels = percent) +
  labs(x = expression(paste("relative estimation error in ", tau^2)),  fill = "Model", color = "Model") +
  theme_bw() +
  geom_vline(data = dummy %>% filter(error_type == "tau"), aes(xintercept = avg, color = model), size = 1) +
  theme(text = element_text(size = 20))

ggplot(dummy %>% filter(error_type == "balance", model != "Bühlmann-Straub"), aes(x = rel_error, fill = model)) +
  geom_density(alpha=.5, fill = "#00BFC4") +
  scale_x_continuous(trans = "pseudo_log", breaks = c(-1, -0.5, -0.25, 0, 0.25, 0.5, 1) , labels = percent) +
  coord_cartesian(xlim = c(-1, 1))+
  labs(x = "relative error in the balance property",  fill = "Model", color = "Model") +
  theme_bw() +
  geom_vline(data = dummy %>% filter(error_type == "balance", model != "Bühlmann-Straub"), aes(xintercept = avg, color = model), size = 1, color = "#00BFC4") +
  theme(text = element_text(size = 20))

# ggplot(dummy %>% filter(error_type == "rho"), aes(x = rel_error, fill = model)) +
#   geom_density(alpha=.5) +
#   labs(x = "average actual correlation", fill = "Model", color = "Model") +
#   theme_bw() +
#   theme(text = element_text(size = 15))

dummy %>% group_by(error_type, model) %>% summarize(med = median(rel_error), avg = mean(rel_error)) #%>% pivot_wider(cols = error_type)


# Estimate model parameters in Bühlmanns model
# Compare relative errors for mu_j (blended), mu, balance property and tau
# Print some data to make sure stuff looks reasonable

# plot(pseudo_log_trans(), xlim = c(-20, 20))
# x <- seq(from = -20, to = 20, length.out = 1000)
# lines(x, asinh(x/2), col = "red")
# asinh(x/2)

# Plot one sim

plot_data <- as_tibble(mu_jt) %>%
  add_column(buhlmann = blended_b,
             proposed = blended,
             actual = mu_j,
             risk = paste0("Cohort ", 1:n_risks)) %>%
  pivot_longer(-c(risk, buhlmann, proposed, actual)) %>%
  mutate(name = as.integer(substring(name, 2))) %>%
  rename(term = name, observed = value) %>%
  pivot_longer(-c(risk, term)) %>%
  mutate(risk = factor(risk, levels = paste0("Cohort ", 1:n_risks))) %>%
  filter(!is.na(value)) %>%
  mutate(name = case_when(
    name == "actual"   ~ "True mean",
    name == "proposed" ~ "Blended proposed",
    name == "buhlmann" ~ "Blended Bühlmann-Straub",
    TRUE ~ "Observed"))

ggplot(plot_data, aes(x = term, y = value, color = name)) +
  geom_line(size = 1) +
  geom_point(data = plot_data %>% filter(name == "Observed"), size = 3) +
  facet_wrap(~risk, scales = "free_y") +
  theme_bw(base_size = 20) +
  scale_x_continuous(breaks = scales::pretty_breaks(n = 5)) +
  labs(x = "Term", y = "Key ratio", color = "")

####################
# Dependency on rho
###################

ggplot(dummy %>% filter(error_type == "mu"), aes(x = rho, y= rel_error, color = model)) +
  geom_point(alpha=.05) +
  stat_smooth() +
  coord_cartesian(ylim = c(-1, 1.5)) +
  scale_y_continuous(trans = "pseudo_log", breaks = c(-1, -0.5, -0.25, 0, 0.25, 0.5, 1, 1.5) , labels = percent) +
  labs(x = "correlation coefficient", y = expression(paste("relative estimation error in ", mu)), color = "Model") +
  theme_bw(base_size = 20)

ggplot(dummy %>% filter(error_type == "mu_j"), aes(x = rho, y= rel_error, color = model)) +
  geom_point(alpha=.05) +
  stat_smooth() +
  coord_cartesian(ylim = c(-1, 1.5)) +
  scale_y_continuous(trans = "pseudo_log", breaks = c(-1, -0.5, -0.25, 0, 0.25, 0.5, 1, 1.5) , labels = percent) +
  labs(x = "correlation coefficient", y = expression(paste("relative estimation error in ", mu[j])), color = "Model") +
  theme_bw(base_size = 20)

ggplot(dummy %>% filter(error_type == "tau"), aes(x = rho, y = rel_error, color = model)) +
  geom_point(alpha=.05) +
  stat_smooth() +
  coord_cartesian(ylim = c(-1, 1.5)) +
  scale_y_continuous(trans = "pseudo_log", breaks = c(-1, -0.5, -0.25, 0, 0.25, 0.5, 1, 1.5) , labels = percent) +
  theme_bw(base_size = 20) +
  labs(x = "correlation coefficient", y = expression(paste("relative estimation error in ", tau^2)), color = "Model")

ggplot(dummy %>% filter(error_type == "balance", model != "Bühlmann"), aes(x = rho, y = rel_error)) +
  geom_point(alpha=.05, color = "#00BFC4") +
  stat_smooth(color = "#00BFC4") +
  coord_cartesian(ylim = c(-1, 1.5)) +
  scale_y_continuous(trans = "pseudo_log", breaks = c(-1, -0.5, -0.25, 0, 0.25, 0.5, 1, 1.5) , labels = percent) +
  theme_bw(base_size = 20) +
  labs(x = "correlation coefficient", y = "relative error in the balance property", color = "")


# Print some tables for the report
xtable(round(w/1e6, 1), digits = 1)
xtable(round(mu_jt, 2), digits = 2)

xtable(cbind(round(rowSums(w)/10000), sigma/sqrt(rowSums(w)), sqrt(diag(sigma_rho)), mu_j, mu_j_hat, mu_hat, mu_b, z, z_b, blended, blended_b))

rho_est <- matrix(nrow = n_risks, ncol = n_risks)
for(i in 1:n_risks){
  for(j in 1:n_risks){
    rho_est[i,j] <- sigma_rho[i,j] / sqrt(diag(sigma_rho)[i]*diag(sigma_rho)[j])
  }
}
rho_est
round(mean(rho_est[lower.tri(rho_est)]),3)


xtable(round(rho_est, 3), digits = 3)


# pseudo_log_trans()
trans_df <- tibble(x = seq(from = -20, to = 20, length.out = 10000),
                   "identity" = x,
                   "log" = log(x),
                   "pseudo log" = asinh(x/2)) %>%
  pivot_longer(-x) %>%
  filter(!is.nan(value)) %>%
  add_row(tibble(x = 0, name = "log", value = -25))

ggplot(trans_df, aes(x = x, y = value, color = name)) +
  geom_line(size = 1) +
  theme_bw(base_size = 20) +
  labs(x = "Untransformed value", y = "Transformed value", color = "Transformation") +
  coord_cartesian(ylim = c(-20, 20))
