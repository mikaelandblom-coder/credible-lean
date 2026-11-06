library(tidyverse)

N <- 1000

get_z <- function(k1, k2, rho) (k1 + 1 - sqrt(k1*k2)*rho)/((k1+1)*(k1+k2+2-2*sqrt(k1*k2)*rho)-(k1+1)*(k2+1)+k1*k2*rho^2)

#k1 <- 5
#k2 <- k1
k1 <- 1
k2 <- 16
rho <- 0.8

#k1 <- seq(0.001, 5, length.out = 1000)
rho <- seq(-1, 1, length.out = N)

z <- get_z(k1, k2, rho)
#z_trans <- pmin(abs(z), 1)
z_trans <- pmax(pmin(z, 1), 0)
#z_trans <- abs(z)

s_scaled_proposed <- ((k1+1)*(k2+1)-k1*k2*rho^2)/(k1+k2+2-2*sqrt(k1*k2)*rho)

# plot(rho, z_trans)
# # lines(rho, 1/(1+k1-sqrt(k1*k2)*rho))
# #plot(rho, ((k1+1)*(k2+1)-k1*k2*rho^2)/(k1+k2+2-2*sqrt(k1*k2)*rho))
# abline(v = (k1+1)/sqrt(k1*k2))


# Two singularities
#
# k1 + k2 + 2 - 2 * sqrt(k1 * k2) * rho = 0
# Equivalent to Var(\hat\mu_1 - \hat\mu_2) = 0 or (k_1 = k_2)
#
# (k1+1)*(k1+k2+2-2*sqrt(k1*k2)*rho)-(k1+1)*(k2+1)+k1*k2*rho^2) = 0
# Equivalent to Var(\hat\mu_1 - \hat\mu) = 0
#

#(k1+1)/sqrt(k1*k2)


# Buhlmann

z_1 <- 1/(1+k1)
z_2 <- 1/(1+k2)
b <- matrix(c(z_1, z_2))/(z_1+z_2)

s_vec <- matrix(nrow = N)
v_vec <- matrix(nrow = N)
for(i in 1:N){
  K_bar_scaled <- matrix(c(k1+1, sqrt(k1*k2)*rho[i], sqrt(k1*k2)*rho[i], k2+1), ncol = 2)
  v_vec[i] <- (K_bar_scaled %*% b)[1]
  s_vec[i] <- t(b) %*% K_bar_scaled %*% b
}

# Plots

s2_scaled <- tibble(rho = rho, 
                    Proposed = s_scaled_proposed,
                    "Bühlmann-Straub" = c(s_vec)) %>%
   pivot_longer(cols = -rho,
                names_to = "Model",
                values_to = "error")

ggplot(s2_scaled, aes(x = rho, y = error, color = Model)) + 
  geom_line(size = 1) +
  theme_bw() +
  geom_vline(xintercept = (k1+1)/sqrt(k1*k2), linetype = "dashed") +
  labs(x = "Correlation coefficient", y = "Expected square error, scaled") +
  theme(text = element_text(size = 15))

ggplot(data.frame(x = rho, y = c(s_vec)-s_scaled_proposed), aes(x,y)) +
  geom_line(size = 1) +
  theme_bw() +
  geom_vline(xintercept = (k1+1)/sqrt(k1*k2), linetype = "dashed") +
  labs(x = "Correlation coefficient", y = "Delta error") +
  theme(text = element_text(size = 15))

cred <- tibble(rho = rho,
               "Proposed" = z,
               "Proposed mod." = z_trans,
               "Bühlmann-Straub" = z_1) %>%
  pivot_longer(cols = -rho,
               names_to = "Model",
               values_to = "error")

ggplot(cred, aes(x = rho, y = error, color = Model)) + 
  geom_line(size = 1) +
  theme_bw() +
  geom_vline(xintercept = (k1+1)/sqrt(k1*k2), linetype = "dashed") +
  labs(x = "Correlation coefficient", y = "Credibility factor") +
  ylim(c(-2, 2)) +
  coord_cartesian(ylim = c(-1.5, 1.5)) +
  theme(text = element_text(size = 15))

# proposed error
b1 <- (k2 + 1 - sqrt(k1*k2)*rho)/(k1 + k2 + 2 - 2 * sqrt(k1*k2)*rho)
e1 <- z^2 * (k1 + 1) + (1-z)^2 * s_scaled_proposed + 1 - 2*z - 2*(1-z)*b1 + 2*z*(1-z)*s_scaled_proposed
e1_mod <- z_trans^2 * (k1 + 1) + (1-z_trans)^2 * s_scaled_proposed + 1 - 2*z_trans - 2*(1-z_trans)*b1 + 2*z_trans*(1-z_trans)*s_scaled_proposed

# Buhlmann error
e1_b <- z_1^2 * (k1 + 1) + (1-z_1)^2 * s_vec + 1 - 2*z_1 - 2*(1-z_1)*b[1] + 2*z_1*(1-z_1)*v_vec

dummy <- tibble(rho = rho,
                Proposed = e1,
                "Proposed mod." = e1_mod,
                "Bühlmann-Straub" = e1_b) %>%
  pivot_longer(cols = -rho,
               names_to = "Model",
               values_to = "error")

ggplot(dummy, aes(x = rho, y = error, color = Model)) +
  geom_line(size = 1) +
  theme_bw() +
  geom_vline(xintercept = (k1+1)/sqrt(k1*k2), linetype = "dashed") +
  labs(x = "Correlation coefficient", y = "Expected square error, scaled") +
  theme(text = element_text(size = 15))



alpha   <- z + b1 - z*b1
alpha_b <- z_1 + b[1] - z_1*b[1]

dummy2 <- tibble(rho = rho,
                 Proposed = alpha,
                 "Bühlmann-Straub" = alpha_b) %>%
  pivot_longer(cols = -rho,
               names_to = "Model",
               values_to = "Weight")
ggplot(dummy2, aes(x = rho, y = Weight, color = Model)) +
  geom_line(size = 1) +
  theme_bw() +
  geom_vline(xintercept = (k1+1)/sqrt(k1*k2), linetype = "dashed") +
  labs(x = "Correlation coefficient", y = "Weight, alpha") +
  theme(text = element_text(size = 15))

beta <- 0.5
alpha <- (1-beta*rho)/(beta^2 + 1 - 2*beta*rho)
plot(rho, alpha)

sig2 <- alpha^2 * beta^2 + (1-alpha)^2 + 2*alpha*(1-alpha)*beta*rho
plot(rho, sig2)

plot(rho, b1, ylim = c(-0.5, 1.5))
lines(x = rho, y=(1-b1))
