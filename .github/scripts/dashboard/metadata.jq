# Metadata of a run for the dashboard: jq -n -f metadata.jq
{
  is_pr: ($ENV.IS_PR == "true"),
  current_commit: $ENV.COMMIT,
  configuration: $ENV.CONFIGURATION,
  commit_message: $ENV.COMMIT_MESSAGE,
  source_branch: $ENV.SRC_BRANCH,
  source_repository: $ENV.SRC_REPO,
  date: $ENV.DATE,
  pipeline_status: $ENV.STATUS,
  url: $ENV.URL
}
+ if $ENV.IS_PR == "true" then {
    pr_number: ($ENV.PR_NUMBER | tonumber),
    pr_title: $ENV.PR_TITLE,
    target_branch: $ENV.TGT_BRANCH,
    target_repository: $ENV.TGT_REPO
  } else {} end
