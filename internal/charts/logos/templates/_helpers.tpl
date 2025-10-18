{{/*
Expand the name of the chart.
*/}}
{{- define "logos.name" -}}
{{- default .Chart.Name .Values.nameOverride | trunc 63 | trimSuffix "-" }}
{{- end }}

{{/*
Create a default fully qualified app name.
*/}}
{{- define "logos.fullname" -}}
{{- if .Values.fullnameOverride }}
{{- .Values.fullnameOverride | trunc 63 | trimSuffix "-" }}
{{- else }}
{{- $name := default .Chart.Name .Values.nameOverride }}
{{- if contains $name .Release.Name }}
{{- .Release.Name | trunc 63 | trimSuffix "-" }}
{{- else }}
{{- printf "%s-%s" .Release.Name $name | trunc 63 | trimSuffix "-" }}
{{- end }}
{{- end }}
{{- end }}

{{/*
Create chart name and version as used by the chart label.
*/}}
{{- define "logos.chart" -}}
{{- printf "%s-%s" .Chart.Name .Chart.Version | replace "+" "_" | trunc 63 | trimSuffix "-" }}
{{- end }}

{{/*
Common labels
*/}}
{{- define "logos.labels" -}}
helm.sh/chart: {{ include "logos.chart" . }}
{{ include "logos.selectorLabels" . }}
{{- if .Chart.AppVersion }}
app.kubernetes.io/version: {{ .Chart.AppVersion | quote }}
{{- end }}
app.kubernetes.io/managed-by: {{ .Release.Service }}
{{- with .Values.commonLabels }}
{{ toYaml . }}
{{- end }}
{{- end }}

{{/*
Selector labels
*/}}
{{- define "logos.selectorLabels" -}}
app.kubernetes.io/name: {{ include "logos.name" . }}
app.kubernetes.io/instance: {{ .Release.Name }}
{{- end }}

{{/*
Component selector labels
*/}}
{{- define "logos.componentSelectorLabels" -}}
{{ include "logos.selectorLabels" . }}
app.kubernetes.io/component: {{ .component }}
{{- end }}

{{/*
Create the name of the service account to use
*/}}
{{- define "logos.serviceAccountName" -}}
{{- if .Values.serviceAccount.create }}
{{- default (include "logos.fullname" .) .Values.serviceAccount.name }}
{{- else }}
{{- default "default" .Values.serviceAccount.name }}
{{- end }}
{{- end }}

{{/*
Generate signing secret name
*/}}
{{- define "logos.signingSecretName" -}}
{{- printf "%s-signing-secret" (include "logos.fullname" .) }}
{{- end }}

{{/*
Generate API signing secret name
*/}}
{{- define "logos.apiSigningSecretName" -}}
{{- printf "%s-api-signing-secret" (include "logos.fullname" .) }}
{{- end }}

{{/*
Tool Router full name
*/}}
{{- define "logos.toolRouter.fullname" -}}
{{- printf "%s-%s" (include "logos.fullname" .) .Values.toolRouter.name }}
{{- end }}

{{/*
LOGOS API full name
*/}}
{{- define "logos.logosApi.fullname" -}}
{{- printf "%s-%s" (include "logos.fullname" .) .Values.logosApi.name }}
{{- end }}

{{/*
Interactive Chat full name
*/}}
{{- define "logos.interactiveChat.fullname" -}}
{{- printf "%s-%s" (include "logos.fullname" .) .Values.interactiveChat.name }}
{{- end }}

{{/*
Redis full name
*/}}
{{- define "logos.redis.fullname" -}}
{{- printf "%s-redis" (include "logos.fullname" .) }}
{{- end }}

{{/*
Generate image reference
*/}}
{{- define "logos.image" -}}
{{- $registry := .Values.global.imageRegistry -}}
{{- $image := .image -}}
{{- $tag := .tag | default .Chart.AppVersion -}}
{{- printf "%s/%s:%s" $registry $image $tag }}
{{- end }}

{{/*
Generate environment variables for signing
*/}}
{{- define "logos.signingEnvVars" -}}
{{- if .Values.global.signingSecret }}
- name: SIGNING_SECRET
  valueFrom:
    secretKeyRef:
      name: {{ include "logos.signingSecretName" . }}
      key: signing-secret
{{- end }}
{{- if .Values.global.apiSigningSecret }}
- name: API_SIGNING_SECRET
  valueFrom:
    secretKeyRef:
      name: {{ include "logos.apiSigningSecretName" . }}
      key: api-signing-secret
{{- end }}
{{- end }}

{{/*
Generate Redis URL
*/}}
{{- define "logos.redisUrl" -}}
{{- if .Values.global.useRedisLimiter }}
{{- printf "redis://%s:6379/0" (include "logos.redis.fullname" .) }}
{{- else }}
{{- "" }}
{{- end }}
{{- end }}
